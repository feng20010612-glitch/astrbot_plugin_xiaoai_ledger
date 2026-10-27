"""AstrBot 插件：通过 HTTP 接入本机「小爱记账」，在 QQ 里记账 / 查账 / 看统计。

设计原则
--------
* 完全不修改小爱记账：只调用它现成的 HTTP 接口（默认 http://127.0.0.1:8899）。
* 分类以它 /api/settings 里的清单为准，不在清单内的一律拒绝，避免把统计口径搞坏。
* 只提供 记账 / 查账 / 月度统计 / 删除 / 看分类，不提供撤销——删错了去它自己的回收站恢复。
"""

from __future__ import annotations

import asyncio
import base64
import io
import json
import os
import re
import subprocess
import tempfile
import time
import zipfile
import urllib.error
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, MessageChain, filter
from astrbot.api.star import Context, Star, register

DEFAULT_BASE = "http://127.0.0.1:8899"
HTTP_TIMEOUT = 6
CACHE_TTL = 60
NL = chr(10)

HELP_LINES = [
    "【小爱记账】用法",
    "· /记 25 午饭            记一笔支出（今天）",
    "· /记 收入 5000 工资     记一笔收入",
    "· /记 支出 25 餐饮/午饭 和同事吃   指定分类/二级 + 备注",
    "· /记 昨天 32 打车       支持 今天/昨天/前天/08-15/2026-08-15",
    "· /查 午饭              按关键词查最近记录",
    "· /查 2026-10           查某个月的记录",
    "· /月                   本月支出/收入/结余",
    "· /月 2026-09           指定月份",
    "· /删 1234              删除某条（进回收站，可去记账本里恢复）",
    "· /类别                 看看有哪些分类可用",
    "· /账本                 显示这条帮助",
]
HELP_TEXT = NL.join(HELP_LINES)

KEYWORD_MAP = [
    ("吃喝饮食", ["早饭", "早餐", "午饭", "午餐", "晚饭", "晚餐", "夜宵", "外卖", "奶茶",
                  "咖啡", "吃饭", "聚餐", "零食", "食堂", "水果", "饮料"]),
    ("交通出行", ["打车", "网约车", "地铁", "公交", "加油", "停车", "高铁", "火车",
                  "机票", "单车", "过路费"]),
    ("居住水电", ["房租", "水电", "电费", "水费", "物业", "燃气", "宽带", "取暖"]),
    ("生活日用", ["日用", "纸巾", "洗发", "牙膏", "洗衣", "超市", "五金"]),
    ("医疗健康", ["看病", "挂号", "买药", "药费", "体检", "牙医", "医院"]),
    ("服饰美容", ["衣服", "裤子", "鞋", "外套", "理发", "护肤", "化妆", "美容", "包包"]),
    ("数码电子", ["手机", "电脑", "耳机", "充电", "键盘", "鼠标", "硬盘"]),
    ("娱乐休闲", ["游戏", "电影", "门票", "会员", "健身", "演出", "KTV"]),
    ("人情社交", ["红包", "礼物", "请客", "份子", "随礼", "聚会"]),
    ("学习提升", ["买书", "课程", "培训", "考试", "网课", "资料"]),
    ("通讯网络", ["话费", "流量", "充话费", "宽带费"]),
]


AMOUNT_RE = re.compile(r"^[¥￥]?(\d+(?:\.\d{1,2})?)(?:元|块|块钱)?$")
DATE_FULL_RE = re.compile(r"^(\d{4})-(\d{1,2})-(\d{1,2})$")
DATE_MD_RE = re.compile(r"^(\d{1,2})-(\d{1,2})$")
DATE_CN_RE = re.compile(r"^(\d{1,2})月(\d{1,2})日?$")
MONTH_RE = re.compile(r"^(\d{4})-(\d{1,2})$")


class LedgerOffline(Exception):
    """记账本没开 / 连不上。"""


class LedgerApiError(Exception):
    """记账本返回了错误。"""


def money(n) -> str:
    try:
        return "%.2f" % float(n)
    except (TypeError, ValueError):
        return str(n)


def today_str() -> str:
    return date.today().strftime("%Y-%m-%d")


@register(
    "astrbot_plugin_xiaoai_ledger",
    "小爱",
    "通过小爱记账的 HTTP 接口在 QQ 里记账、查账、看月度统计（不改动记账本本身）",
    "1.5.1",
)
class XiaoaiLedgerPlugin(Star):
    def __init__(self, context: Context, config=None):
        super().__init__(context)
        self.config = config if hasattr(config, "get") else {}
        self._settings_cache = (0.0, None)
        self._lock = asyncio.Lock()

    # ───────────────────────── 配置 ─────────────────────────
    def _cfg(self, key, default=""):
        try:
            v = self.config.get(key, default)
        except Exception:
            return default
        return default if v is None else v

    def _base(self) -> str:
        return str(self._cfg("base_url", DEFAULT_BASE) or DEFAULT_BASE).rstrip("/")

    def _allow_ids(self) -> set:
        raw = str(self._cfg("allow_ids", "") or "")
        return {x.strip() for x in re.split(r"[,，\s]+", raw) if x.strip()}

    def _sender_id(self, event) -> str:
        for attr in ("get_sender_id", "get_sender_id_str"):
            fn = getattr(event, attr, None)
            if callable(fn):
                try:
                    sid = fn()
                    if sid:
                        return str(sid)
                except Exception:
                    pass
        return ""

    def _denied(self, event) -> str:
        allow = self._allow_ids()
        sid = self._sender_id(event)
        if allow and sid not in allow:
            return "当前账号不在允许名单里，请联系部署者。"
        if self._cfg("only_private", False):
            getter = getattr(event, "get_group_id", None)
            try:
                gid = getter() if callable(getter) else ""
            except Exception:
                gid = ""
            if gid:
                return "记账这些事只在私聊里做喵，群里不方便。"
        return ""

    # ───────────────────────── HTTP ─────────────────────────
    def _request(self, method, path, body=None, params=None):
        url = self._base() + path
        if params:
            clean = {k: v for k, v in params.items() if v not in (None, "")}
            if clean:
                url += "?" + urllib.parse.urlencode(clean)
        data = None
        headers = {"Accept": "application/json"}
        if body is not None:
            data = json.dumps(body, ensure_ascii=False).encode("utf-8")
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
                raw = resp.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as exc:
            raw = exc.read().decode("utf-8", "replace")
            msg = raw[:160]
            try:
                parsed = json.loads(raw)
                if isinstance(parsed, dict) and parsed.get("error"):
                    msg = str(parsed["error"])
            except Exception:
                pass
            raise LedgerApiError(msg)
        except Exception as exc:
            logger.warning("[xiaoai_ledger] %s %s 失败: %s", method, path, exc)
            raise LedgerOffline(url)
        if not raw.strip():
            return {}
        try:
            return json.loads(raw)
        except Exception:
            return {"raw": raw}

    async def _api(self, method, path, body=None, params=None):
        async with self._lock:
            return await asyncio.to_thread(self._request, method, path, body, params)

    def _ping(self) -> bool:
        try:
            self._request("GET", "/api/version")
            return True
        except Exception:
            return False

    def _exe_path(self) -> str:
        return str(self._cfg("exe_path", "") or "").strip()

    def _start_exe(self) -> bool:
        """按配置把记账本拉起来（不弹浏览器、不弹控制台）。"""
        if not bool(self._cfg("auto_start", False)):
            return False
        exe = self._resolved_exe()
        if not exe or not os.path.isfile(exe):
            logger.warning("[xiaoai_ledger] 想自动启动但找不到程序: %s", exe or "(未配置)")
            return False
        env = dict(os.environ)
        env["XIAOAI_NO_BROWSER"] = "1"
        flags = 0
        if hasattr(subprocess, "CREATE_NO_WINDOW"):
            flags |= subprocess.CREATE_NO_WINDOW
        if hasattr(subprocess, "DETACHED_PROCESS"):
            flags |= subprocess.DETACHED_PROCESS
        try:
            subprocess.Popen(
                [exe],
                cwd=os.path.dirname(exe) or None,
                env=env,
                close_fds=True,
                creationflags=flags,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            logger.info("[xiaoai_ledger] 已尝试启动记账本: %s", exe)
            return True
        except Exception as exc:
            logger.warning("[xiaoai_ledger] 启动失败: %s", exc)
            return False

    def _ensure_online(self) -> bool:
        if self._ping():
            return True
        if not self._start_exe():
            return False
        try:
            timeout = float(self._cfg("start_timeout", 20) or 20)
        except (TypeError, ValueError):
            timeout = 20.0
        deadline = time.time() + max(3.0, timeout)
        while time.time() < deadline:
            time.sleep(0.8)
            if self._ping():
                return True
        return False

    # ───────────────────────── 程序安装状态 ─────────────────────────
    def _state_file(self) -> str:
        base = ""
        try:
            base = str(StarTools.get_data_dir("astrbot_plugin_xiaoai_ledger"))
        except Exception:
            base = ""
        if not base:
            base = os.path.join(tempfile.gettempdir(), "astrbot_plugin_xiaoai_ledger")
        os.makedirs(base, exist_ok=True)
        return os.path.join(base, "app_state.json")

    def _load_state(self) -> dict:
        try:
            with open(self._state_file(), "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _save_state(self, data: dict) -> None:
        try:
            with open(self._state_file(), "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as exc:
            logger.warning("[xiaoai_ledger] 保存安装状态失败: %s", exc)

    def _resolved_exe(self) -> str:
        """配置里的 exe_path 优先，其次上次装好的路径。"""
        exe = self._exe_path()
        if exe and os.path.isfile(exe):
            return exe
        saved = str(self._load_state().get("exe_path") or "")
        return saved if saved and os.path.isfile(saved) else ""

    async def _call(self, method, path, body=None, params=None):
        """统一入口：连不上时按配置尝试拉起一次，然后重试。"""
        try:
            return await self._api(method, path, body, params)
        except LedgerOffline:
            if not await asyncio.to_thread(self._ensure_online):
                raise
            return await self._api(method, path, body, params)

    async def _settings(self, force=False):
        ts, cached = self._settings_cache
        if cached is not None and not force and time.time() - ts < CACHE_TTL:
            return cached
        data = await self._call("GET", "/api/settings")
        self._settings_cache = (time.time(), data)
        return data

    # ───────────────────────── 分类 ─────────────────────────
    async def _cats(self):
        try:
            s = await self._settings()
        except (LedgerOffline, LedgerApiError):
            return [], [], {}
        expense = list(s.get("expenseCats") or [])
        income = list(s.get("incomeCats") or [])
        subs = s.get("subCats") or {}
        if not isinstance(subs, dict):
            subs = {}
        return expense, income, subs

    @staticmethod
    def _guess_category(text, kind, expense, income, subs, fallback):
        pool = [str(c) for c in (expense if kind == "expense" else income)]
        # 1) 文本里直接出现二级分类名 -> 取它的父分类
        best_cat, best_sub = "", ""
        for cat, lst in (subs or {}).items():
            for sub in lst or []:
                sub = str(sub)
                if sub and sub in text and (not pool or str(cat) in pool):
                    if len(sub) > len(best_sub):
                        best_cat, best_sub = str(cat), sub
        if best_cat:
            return best_cat, best_sub
        # 2) 文本里直接出现一级分类名
        for cat in pool:
            if cat and cat in text:
                return cat, ""
        # 3) 生活化关键词（只在记账本真有这个分类时才用）
        for cat, words in KEYWORD_MAP:
            if pool and cat not in pool:
                continue
            for w in words:
                if w in text:
                    return cat, ""
        # 4) 兜底：优先"其他"类，再不行取第一个
        for cat in pool:
            if "其他" in cat:
                return cat, ""
        if fallback in pool:
            return fallback, ""
        return (pool[0] if pool else fallback), ""

    # ───────────────────────── 解析工具 ─────────────────────────
    @staticmethod
    def _payload(event, words) -> str:
        text = (getattr(event, "message_str", "") or "").strip()
        for pre in ("/", "／", "#"):
            if text.startswith(pre):
                text = text[len(pre):].strip()
                break
        for w in words:
            if text.startswith(w):
                text = text[len(w):].strip()
                break
        return text

    @staticmethod
    def _parse_date(token) -> str:
        token = (token or "").strip()
        today = date.today()
        if token in ("今天", "今日"):
            return today.strftime("%Y-%m-%d")
        if token == "昨天":
            return (today - timedelta(days=1)).strftime("%Y-%m-%d")
        if token == "前天":
            return (today - timedelta(days=2)).strftime("%Y-%m-%d")
        for pattern in (DATE_FULL_RE, DATE_CN_RE, DATE_MD_RE):
            m = pattern.match(token)
            if not m:
                continue
            try:
                if len(m.groups()) == 3:
                    return date(int(m.group(1)), int(m.group(2)), int(m.group(3))).strftime("%Y-%m-%d")
                return date(today.year, int(m.group(1)), int(m.group(2))).strftime("%Y-%m-%d")
            except ValueError:
                return ""
        return ""

    # ───────────────────────── 记一笔 ─────────────────────────
    @filter.command("记")
    async def cmd_add(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        text = self._payload(event, ("记账", "记"))
        if not text:
            yield event.plain_result("要记多少喵？例如：/记 25 午饭")
            return

        expense, income, subs = await self._cats()
        if not expense and not income:
            yield event.plain_result("连不上记账本喵，自动启动也没成功（检查程序路径配置）。")
            return

        kind = "expense"
        tokens = text.split()
        if tokens and tokens[0] in ("收入", "收", "入账"):
            kind = "income"
            tokens = tokens[1:]
        elif tokens and tokens[0] in ("支出", "支", "花"):
            tokens = tokens[1:]

        amount = None
        date_str = today_str()
        cat_hint = ""
        rest = []
        for tok in tokens:
            if amount is None:
                m = AMOUNT_RE.match(tok)
                if m:
                    amount = float(m.group(1))
                    continue
            parsed_date = self._parse_date(tok)
            if parsed_date:
                date_str = parsed_date
                continue
            if "/" in tok or "／" in tok:
                cat_hint = tok.replace("／", "/")
                continue
            rest.append(tok)

        note = " ".join(rest).strip()
        if amount is None:
            m = re.search(r"(\d+(?:\.\d{1,2})?)", text)
            if m:
                amount = float(m.group(1))
                note = (note.replace(m.group(0), "")).strip()
        if amount is None or amount <= 0:
            yield event.plain_result("没看懂金额喵，例如：/记 25 午饭")
            return

        fallback = str(self._cfg("default_category", "其他") or "其他")
        category, sub = "", ""
        if cat_hint:
            head, _, tail = cat_hint.partition("/")
            head, tail = head.strip(), tail.strip()
            pool = expense if kind == "expense" else income
            if head in pool:
                category, sub = head, tail
            elif tail in pool:
                category, sub = tail, head
            else:
                for cat, lst in subs.items():
                    if head in [str(x) for x in (lst or [])]:
                        category, sub = str(cat), head
                        break
            if not category:
                yield event.plain_result(
                    "「%s」不在记账本的分类里喵。发 /类别 看看能用的。" % cat_hint
                )
                return
        else:
            category, sub = self._guess_category(
                note + " " + text, kind, expense, income, subs, fallback
            )

        pool = expense if kind == "expense" else income
        if pool and category not in pool:
            category = pool[0]
        if not sub:
            for cand in (subs.get(category) or []):
                cand = str(cand)
                if cand and cand in (note + " " + text):
                    sub = cand
                    break

        try:
            rec = await self._call(
                "POST",
                "/api/records",
                {
                    "date": date_str,
                    "type": kind,
                    "category": category,
                    "sub": sub,
                    "amount": round(amount, 2),
                    "note": note,
                },
            )
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵，自动启动也没成功（检查程序路径配置）。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return

        rid = rec.get("id", "?")
        self._remember_last(event, rid)
        label = "收入" if kind == "income" else "支出"
        cat_text = category + (("/" + sub) if sub else "")
        tail = ("，备注：" + note) if note else ""
        msg = ("记好了喵：%s %s %s %s 元%s（#%s）" % (date_str, label, cat_text, money(amount), tail, rid)
               + NL + "要改说 /改 金额，要删说 /改 删。")
        if kind == "expense":
            spent = await self._month_spent(date_str[:7])
            warn = await self._budget_warning(date_str[:7], spent)
            if warn:
                msg += NL + warn
        yield event.plain_result(msg)

    # ───────────────────────── 查账 ─────────────────────────
    @filter.command("查")
    async def cmd_query(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        text = self._payload(event, ("查询", "查"))
        month, search = "", text.strip()
        m = MONTH_RE.match(search)
        if m:
            month = "%04d-%02d" % (int(m.group(1)), int(m.group(2)))
            search = ""
        try:
            rows = await self._call(
                "GET", "/api/records", params={"month": month, "search": search, "limit": 15}
            )
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵，自动启动也没成功（检查程序路径配置）。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return
        if not isinstance(rows, list) or not rows:
            yield event.plain_result("没查到符合条件的记录喵。")
            return
        lines = ["查到 %d 条（最多显示 15 条）：" % len(rows)]
        total_out = total_in = 0.0
        for r in rows:
            amt = float(r.get("amount") or 0)
            if r.get("type") == "income":
                total_in += amt
                sign = "+"
            else:
                total_out += amt
                sign = "-"
            cat = str(r.get("category") or "")
            sub = str(r.get("sub") or "")
            note = str(r.get("note") or "")
            parts = ["#" + str(r.get("id", "?")), str(r.get("date") or "")[5:], sign + money(amt), cat]
            if sub:
                parts.append("/" + sub)
            if note:
                parts.append(note)
            lines.append(" ".join(parts))
        lines.append("合计：支出 %s 元，收入 %s 元" % (money(total_out), money(total_in)))
        yield event.plain_result(NL.join(lines))

    # ───────────────────────── 月度统计 ─────────────────────────
    @filter.command("月")
    async def cmd_month(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        text = self._payload(event, ("月度", "月")).strip()
        if text:
            m = MONTH_RE.match(text)
            if not m:
                yield event.plain_result("月份写成 2026-09 这样喵。")
                return
            month = "%04d-%02d" % (int(m.group(1)), int(m.group(2)))
        else:
            month = date.today().strftime("%Y-%m")
        try:
            rows = await self._call("GET", "/api/records", params={"month": month})
            budget = await self._call("GET", "/api/budget")
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵，自动启动也没成功（检查程序路径配置）。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return

        out = inn = 0.0
        per_cat = {}
        for r in rows or []:
            amt = float(r.get("amount") or 0)
            if r.get("type") == "income":
                inn += amt
            else:
                out += amt
                key = str(r.get("category") or "其他")
                per_cat[key] = per_cat.get(key, 0.0) + amt

        lines = ["【%s】" % month,
                 "支出 %s 元 · 收入 %s 元 · 结余 %s 元" % (money(out), money(inn), money(inn - out))]
        limit = 0.0
        if isinstance(budget, dict):
            raw = budget.get(month) or budget.get("default")
            try:
                limit = float(raw) if raw not in (None, "") else 0.0
            except (TypeError, ValueError):
                limit = 0.0
            if month in (budget.get("off") or []):
                limit = 0.0
            off_from = budget.get("offFrom") or ""
            if off_from and month >= str(off_from):
                limit = 0.0
        if limit > 0:
            left = limit - out
            pct = out / limit * 100 if limit else 0
            if left >= 0:
                lines.append("预算 %s 元，已用 %.1f%%，还剩 %s 元" % (money(limit), pct, money(left)))
            else:
                lines.append("预算 %s 元，已用 %.1f%%，超支 %s 元" % (money(limit), pct, money(-left)))
        if per_cat:
            top = sorted(per_cat.items(), key=lambda kv: kv[1], reverse=True)[:5]
            lines.append("花得最多：" + "、".join("%s %s" % (k, money(v)) for k, v in top))
        if not rows:
            lines.append("这个月还没有记录喵。")
        yield event.plain_result(NL.join(lines))

    # ───────────────────────── 删除 ─────────────────────────
    @filter.command("删")
    async def cmd_delete(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        text = self._payload(event, ("删除", "删")).strip().lstrip("#")
        if not text.isdigit():
            yield event.plain_result("要给编号喵，例如：/删 1234（编号在记账后的回执里）")
            return
        rid = int(text)
        try:
            res = await self._call("DELETE", "/api/records", {"ids": [rid]})
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵，自动启动也没成功（检查程序路径配置）。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return
        if not res.get("deleted"):
            yield event.plain_result("没找到 #%s 这条记录喵。" % rid)
            return
        rec = (res.get("deletedRecords") or [{}])[0]
        msg = ("删掉了 #%s：%s %s %s 元。" % (rid, str(rec.get("date") or ""),
                                          str(rec.get("category") or ""), money(rec.get("amount")))
               + NL + "已经进回收站了，反悔可以到记账本的回收站里恢复。")
        yield event.plain_result(msg)

    # ───────────────────────── 分类清单 ─────────────────────────
    @filter.command("类别")
    async def cmd_cats(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        expense, income, subs = await self._cats()
        if not expense and not income:
            yield event.plain_result("连不上记账本喵，自动启动也没成功（检查程序路径配置）。")
            return
        lines = ["【支出】" + "、".join(str(x) for x in expense)]
        if income:
            lines.append("【收入】" + "、".join(str(x) for x in income))
        with_sub = [(c, subs.get(c) or []) for c in expense if subs.get(c)]
        if with_sub:
            lines.append("【二级分类】")
            for c, lst in with_sub[:12]:
                lines.append("· %s：%s" % (c, "/".join(str(x) for x in lst)))
        yield event.plain_result(NL.join(lines))

    # ───────────────────────── 待还提醒 ─────────────────────────
    def _remaining_periods(self, item, today) -> int:
        end = re.match(r"^(\d{4})-(\d{2})", str(item.get("end") or ""))
        if not end:
            return 0
        ey, em = int(end.group(1)), int(end.group(2))
        sy, sm = today.year, today.month
        start = re.match(r"^(\d{4})-(\d{2})", str(item.get("start") or ""))
        if start:
            yy, mm = int(start.group(1)), int(start.group(2))
            if yy * 12 + (mm - 1) > sy * 12 + (sm - 1):
                sy, sm = yy, mm
        left = (ey * 12 + em - 1) - (sy * 12 + sm - 1) + 1
        if left < 0:
            left = 0
        try:
            cap = int(item.get("periods") or 0)
        except (TypeError, ValueError):
            cap = 0
        if cap > 0 and left > cap:
            left = cap
        return left

    def _next_due(self, item, today):
        try:
            day = int(item.get("day") or 1)
        except (TypeError, ValueError):
            day = 1
        if str(item.get("freq") or "") == "yearly":
            try:
                mo = int(item.get("month") or 1)
            except (TypeError, ValueError):
                mo = 1
            y = today.year
            if mo < today.month or (mo == today.month and day < today.day):
                y += 1
            return self._safe_date(y, mo, day)
        y, m = today.year, today.month
        if day < today.day:
            m += 1
            if m > 12:
                m = 1
                y += 1
        return self._safe_date(y, m, day)

    @staticmethod
    def _safe_date(y, m, d):
        import calendar
        last = calendar.monthrange(y, m)[1]
        return date(y, m, min(max(d, 1), last))

    async def _due_items(self, lead_days: int):
        """返回未来 lead_days 天内要还的账单列表。"""
        try:
            data = await self._call("GET", "/api/recurring")
        except (LedgerOffline, LedgerApiError):
            return []
        items = data if isinstance(data, list) else (data or {}).get("items") or []
        today = date.today()
        out = []
        for it in items or []:
            if not isinstance(it, dict):
                continue
            if it.get("enabled") is False:
                continue
            if str(it.get("type") or "expense") != "expense":
                continue
            try:
                amount = float(it.get("amount") or 0)
            except (TypeError, ValueError):
                continue
            if amount <= 0:
                continue
            try:
                periods = int(it.get("periods") or 1)
            except (TypeError, ValueError):
                periods = 1
            due = self._next_due(it, today)
            left = self._remaining_periods(it, today) if periods >= 2 else 0
            if periods >= 2 and left <= 0:
                continue
            delta = (due - today).days
            if 0 <= delta <= lead_days:
                out.append({
                    "name": str(it.get("name") or "账单"),
                    "due": due.strftime("%Y-%m-%d"),
                    "in_days": delta,
                    "amount": amount,
                    "left": left,
                })
        out.sort(key=lambda x: x["due"])
        return out

    async def _maybe_remind(self) -> None:
        if not bool(self._cfg("remind_enabled", True)):
            return
        try:
            hour = int(self._cfg("notify_hour", 9) or 9)
        except (TypeError, ValueError):
            hour = 9
        now = datetime.now()
        if now.hour < hour:
            return
        st = self._load_state()
        today_key = now.strftime("%Y-%m-%d")
        if st.get("remind_sent") == today_key:
            return
        try:
            lead = int(self._cfg("lead_days", 3) or 3)
        except (TypeError, ValueError):
            lead = 3
        items = await self._due_items(max(0, lead))
        if not items:
            st["remind_sent"] = today_key
            self._save_state(st)
            return
        origin = self._target_origin()
        if not origin:
            logger.info("[xiaoai_ledger] 有 %d 笔待还，但还不知道推给谁（先在 QQ 里发一次任意记账指令）", len(items))
            return
        lines = ["【待还提醒】%d 笔" % len(items)]
        for it in items:
            when = "今天" if it["in_days"] == 0 else ("%d 天后" % it["in_days"])
            extra = ("，剩 %d 期" % it["left"]) if it["left"] else ""
            lines.append("· %s %s（%s）%s 元%s" % (it["name"], it["due"], when, money(it["amount"]), extra))
        text = NL.join(lines)
        try:
            chain = MessageChain().message(text)
            ok = await self.context.send_message(origin, chain)
            if ok is False:
                logger.warning("[xiaoai_ledger] 待还提醒发送失败")
                return
        except Exception as exc:
            logger.warning("[xiaoai_ledger] 待还提醒发送异常: %s", exc)
            return
        st["remind_sent"] = today_key
        self._save_state(st)

    async def _reminder_loop(self) -> None:
        await asyncio.sleep(20)
        while True:
            try:
                await self._maybe_remind()
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                logger.warning("[xiaoai_ledger] 提醒循环出错: %s", exc)
            await asyncio.sleep(1800)

    async def initialize(self) -> None:
        self._remind_task = asyncio.create_task(self._reminder_loop())

    async def terminate(self) -> None:
        task = getattr(self, "_remind_task", None)
        if task is not None:
            task.cancel()
            try:
                await task
            except Exception:
                pass

    # ───────────────────────── 改上一笔 ─────────────────────────
    @filter.command("改")
    async def cmd_edit(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        text = self._payload(event, ("修改", "改")).strip()
        rid = self._last_id(event)
        if rid is None:
            yield event.plain_result("还没记住你上次记的那笔喵，先 /记 一笔再来改。")
            return
        if not text:
            yield event.plain_result("要改什么喵？例如：/改 30（改金额） 或 /改 备注 和同事吃")
            return
        body = {"id": rid}
        tokens = text.split()
        if tokens and tokens[0] in ("删", "删除", "不要了"):
            try:
                res = await self._call("DELETE", "/api/records", {"ids": [rid]})
            except LedgerOffline:
                yield event.plain_result("连不上记账本喵。")
                return
            except LedgerApiError as exc:
                yield event.plain_result("记账本说：%s" % exc)
                return
            if res.get("deleted"):
                yield event.plain_result("已删掉 #%s，进回收站了；要救回来发 /恢复。" % rid)
            else:
                yield event.plain_result("没找到 #%s 这条了喵。" % rid)
            return
        m = AMOUNT_RE.match(tokens[0]) if tokens else None
        if m:
            body["amount"] = round(float(m.group(1)), 2)
            rest = " ".join(tokens[1:]).strip()
            if rest:
                body["note"] = rest
        else:
            body["note"] = text
        try:
            await self._call("PUT", "/api/records", body)
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return
        parts = []
        if "amount" in body:
            parts.append("金额 %s 元" % money(body["amount"]))
        if "note" in body:
            parts.append("备注「%s」" % body["note"])
        yield event.plain_result("改好了 #%s：%s。" % (rid, "，".join(parts) or "已更新"))

    # ───────────────────────── 恢复回收站 ─────────────────────────
    @filter.command("恢复")
    async def cmd_restore(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        text = self._payload(event, ("恢复",)).strip().lstrip("#")
        try:
            data = await self._call("GET", "/api/trash")
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return
        records = (data or {}).get("records") if isinstance(data, dict) else None
        records = records or []
        if not records:
            yield event.plain_result("回收站是空的喵。")
            return
        records = sorted(records, key=lambda x: x.get("deletedAt") or 0, reverse=True)
        if not text:
            lines = ["回收站有 %d 条（发 /恢复 编号 救回来）：" % len(records)]
            for i, r in enumerate(records[:10], 1):
                note = str(r.get("note") or "")
                sub = str(r.get("sub") or "")
                lines.append("%d. #%s %s %s%s %s 元%s" % (
                    i, r.get("id", "?"), str(r.get("date") or "")[5:],
                    str(r.get("category") or ""), ("/" + sub) if sub else "",
                    money(r.get("amount")), (" " + note) if note else ""))
            yield event.plain_result(NL.join(lines))
            return
        if not text.isdigit():
            yield event.plain_result("要发编号喵，例如 /恢复 1（编号看上一条列表）")
            return
        idx = int(text) - 1
        if idx < 0 or idx >= len(records):
            yield event.plain_result("没有这个编号喵，回收站一共 %d 条。" % len(records))
            return
        rec = dict(records[idx])
        rest = [x for x in records if x.get("id") != rec.get("id")]
        try:
            await self._call("POST", "/api/import", {"records": [rec]})
            await self._call("PUT", "/api/trash", {"records": rest})
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("恢复失败：%s" % exc)
            return
        yield event.plain_result("已恢复 #%s：%s %s %s 元。" % (
            rec.get("id", "?"), str(rec.get("date") or ""),
            str(rec.get("category") or ""), money(rec.get("amount"))))

    # ───────────────────────── 状态 ─────────────────────────
    @filter.command("账本状态")
    async def cmd_status(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        lines = ["服务地址：" + self._base()]
        try:
            ver = await self._call("GET", "/api/version")
            rows = await self._call("GET", "/api/records")
        except LedgerOffline:
            yield event.plain_result("连不上记账本喵：" + self._base() + "（自动启动也没成功）")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return
        lines.append("版本：" + str(ver.get("runningVersion") or ver.get("appVersion") or "?"))
        total = len(rows) if isinstance(rows, list) else 0
        lines.append("记录总数：%d 条" % total)
        month = date.today().strftime("%Y-%m")
        out = inn = 0.0
        for r in rows or []:
            if str(r.get("date") or "").startswith(month):
                amt = float(r.get("amount") or 0)
                if r.get("type") == "income":
                    inn += amt
                else:
                    out += amt
        lines.append("本月支出 %s / 收入 %s" % (money(out), money(inn)))
        auto = bool(self._cfg("auto_start", False))
        exe = self._exe_path()
        if auto:
            lines.append("自动启动：开" + (("（" + exe + "）") if exe else "（未配置路径，实际不会启动）"))
        else:
            lines.append("自动启动：关")
        lines.append("多开时看「记录总数」和地址，就能认出连的是哪个账本。")
        yield event.plain_result(NL.join(lines))

    # ───────────────────────── 自然语言（LLM 工具） ─────────────────────────
    async def _tool_add(self, amount_text, kind_text, category, sub, note, date_text, event=None) -> str:
        try:
            amount = float(str(amount_text).replace("元", "").replace("块", "").strip())
        except (TypeError, ValueError):
            return "金额没看懂，请给出纯数字（例如 25 或 25.5）。"
        if amount <= 0:
            return "金额必须大于 0。"

        expense, income, subs = await self._cats()
        if not expense and not income:
            return "连不上小爱记账（127.0.0.1:8899），先把记账本打开。"

        kind = "income" if str(kind_text or "").strip() in ("收入", "收", "income", "入账") else "expense"
        pool = expense if kind == "expense" else income
        category = str(category or "").strip()
        sub = str(sub or "").strip()
        note = str(note or "").strip()

        # 分类可能是二级名
        if category and category not in pool:
            for cat, lst in subs.items():
                if category in [str(x) for x in (lst or [])] and str(cat) in pool:
                    category, sub = str(cat), (sub or category)
                    break
        if not category:
            guess, gsub = self._guess_category(note + " " + sub, kind, expense, income, subs, "")
            category, sub = guess, (sub or gsub)
        if category not in pool:
            others = [c for c in pool if "其他" in str(c)]
            category = others[0] if others else (pool[0] if pool else "")
        if sub:
            allowed = [str(x) for x in (subs.get(category) or [])]
            if allowed and sub not in allowed:
                sub = ""

        date_str = self._parse_date(date_text) if str(date_text or "").strip() else ""
        if not date_str:
            date_str = today_str()

        try:
            rec = await self._call("POST", "/api/records", {
                "date": date_str,
                "type": kind,
                "category": category,
                "sub": sub,
                "amount": round(amount, 2),
                "note": note,
            })
        except LedgerOffline:
            return "连不上小爱记账，先把记账本打开。"
        except LedgerApiError as exc:
            return "记账本说：%s" % exc

        label = "收入" if kind == "income" else "支出"
        cat_text = category + (("/" + sub) if sub else "")
        tail = ("，备注：" + note) if note else ""
        if event is not None:
            self._remember_last(event, rec.get("id"))
        return ("已记账：#%s %s %s %s %s 元%s"
                % (rec.get("id", "?"), date_str, label, cat_text, money(amount), tail))

    @filter.llm_tool(name="ledger_add")
    async def tool_add(self, event: AstrMessageEvent, amount: str = "", kind: str = "支出",
                       category: str = "", sub: str = "", note: str = "", date: str = "") -> str:
        """
        记一笔账。用户说"记一笔""帮我记""午饭 25""打车花了 23""工资到账 5000"这类话时调用。
        分类不用硬猜，留空会自动按备注判断；只有用户明确说了分类才填。
        Args:
            amount(string): 金额数字，例如 25 或 25.5
            kind(string): 支出 或 收入，默认支出
            category(string): 一级分类，必须是小爱记账里已有的分类，不确定留空
            sub(string): 二级分类，不确定留空
            note(string): 备注，例如 午饭 / 打车 / 房租
            date(string): 日期，可写 今天/昨天/前天/2026-08-15/08-15，留空表示今天
        """
        return await self._tool_add(amount, kind, category, sub, note, date, event=event)

    @filter.llm_tool(name="ledger_query")
    async def tool_query(self, event: AstrMessageEvent, keyword: str = "",
                         month: str = "", limit: str = "10") -> str:
        """
        查账。用户问"我最近记了什么""这个月吃饭花了多少""查一下打车"时调用。
        Args:
            keyword(string): 关键词，匹配分类或备注，可为空
            month(string): 月份，格式 2026-10，可为空表示不限
            limit(string): 最多返回几条，默认 10
        """
        try:
            n = max(1, min(30, int(str(limit or "10"))))
        except (TypeError, ValueError):
            n = 10
        month = str(month or "").strip()
        if month and not MONTH_RE.match(month):
            return "月份格式要写成 2026-10。"
        try:
            rows = await self._call("GET", "/api/records",
                                    params={"month": month, "search": str(keyword or "").strip(),
                                            "limit": n})
        except LedgerOffline:
            return "连不上小爱记账，先把记账本打开。"
        except LedgerApiError as exc:
            return "记账本说：%s" % exc
        if not isinstance(rows, list) or not rows:
            return "没有匹配的记录。"
        out = inn = 0.0
        lines = []
        for r in rows[:n]:
            amt = float(r.get("amount") or 0)
            sign = "+" if r.get("type") == "income" else "-"
            if r.get("type") == "income":
                inn += amt
            else:
                out += amt
            cat = str(r.get("category") or "")
            sub = str(r.get("sub") or "")
            note = str(r.get("note") or "")
            parts = ["#" + str(r.get("id", "?")), str(r.get("date") or ""), sign + money(amt), cat]
            if sub:
                parts.append("/" + sub)
            if note:
                parts.append(note)
            lines.append(" ".join(parts))
        head = "共 %d 条：支出 %s 元、收入 %s 元" % (len(rows), money(out), money(inn))
        return head + NL + NL.join(lines)

    @filter.llm_tool(name="ledger_month")
    async def tool_month(self, event: AstrMessageEvent, month: str = "") -> str:
        """
        月度统计。用户问"这个月花了多少""上月结余多少""预算还剩多少"时调用。
        Args:
            month(string): 月份，格式 2026-10；留空表示本月
        """
        month = str(month or "").strip()
        if month and not MONTH_RE.match(month):
            return "月份格式要写成 2026-10。"
        if not month:
            month = date.today().strftime("%Y-%m")
        try:
            rows = await self._call("GET", "/api/records", params={"month": month})
            budget = await self._call("GET", "/api/budget")
        except LedgerOffline:
            return "连不上小爱记账，先把记账本打开。"
        except LedgerApiError as exc:
            return "记账本说：%s" % exc
        out = inn = 0.0
        per_cat = {}
        for r in rows or []:
            amt = float(r.get("amount") or 0)
            if r.get("type") == "income":
                inn += amt
            else:
                out += amt
                key = str(r.get("category") or "其他")
                per_cat[key] = per_cat.get(key, 0.0) + amt
        lines = ["%s：支出 %s 元，收入 %s 元，结余 %s 元"
                 % (month, money(out), money(inn), money(inn - out))]
        limit = 0.0
        if isinstance(budget, dict):
            raw = budget.get(month) or budget.get("default")
            try:
                limit = float(raw) if raw not in (None, "") else 0.0
            except (TypeError, ValueError):
                limit = 0.0
            if month in (budget.get("off") or []):
                limit = 0.0
            off_from = budget.get("offFrom") or ""
            if off_from and month >= str(off_from):
                limit = 0.0
        if limit > 0:
            left = limit - out
            lines.append("预算 %s 元，已用 %.1f%%，%s"
                         % (money(limit), out / limit * 100,
                            ("还剩 " + money(left) + " 元") if left >= 0 else ("超支 " + money(-left) + " 元")))
        if per_cat:
            top = sorted(per_cat.items(), key=lambda kv: kv[1], reverse=True)[:5]
            lines.append("花得最多：" + "、".join("%s %s" % (k, money(v)) for k, v in top))
        if not rows:
            lines.append("这个月还没有记录。")
        return NL.join(lines)

    @filter.llm_tool(name="ledger_categories")
    async def tool_categories(self, event: AstrMessageEvent) -> str:
        """
        查看记账本里有哪些分类和二级分类。用户问"有哪些分类""能记哪些类"或你不确定分类名时调用。
        """
        expense, income, subs = await self._cats()
        if not expense and not income:
            return "连不上小爱记账，先把记账本打开。"
        lines = ["支出分类：" + "、".join(str(x) for x in expense)]
        if income:
            lines.append("收入分类：" + "、".join(str(x) for x in income))
        for cat, lst in subs.items():
            if lst:
                lines.append("%s 的二级：%s" % (cat, "、".join(str(x) for x in lst)))
        return NL.join(lines)

    # ───────────────────────── 会话与上次记录 ─────────────────────────
    def _remember_origin(self, event) -> None:
        """记住最近一次说话的会话，供主动推送使用。"""
        try:
            umo = getattr(event, "unified_msg_origin", "") or ""
        except Exception:
            umo = ""
        if not umo:
            return
        st = self._load_state()
        if st.get("last_origin") != umo:
            st["last_origin"] = umo
            self._save_state(st)

    def _target_origin(self, event=None) -> str:
        cfg = str(self._cfg("notify_target", "") or "").strip()
        if cfg:
            return cfg
        if event is not None:
            try:
                umo = getattr(event, "unified_msg_origin", "") or ""
            except Exception:
                umo = ""
            if umo:
                return umo
        return str(self._load_state().get("last_origin") or "")

    def _remember_last(self, event, rid) -> None:
        try:
            rid = int(rid)
        except (TypeError, ValueError):
            return
        sid = self._sender_id(event) or "default"
        st = self._load_state()
        last = st.get("last") or {}
        last[str(sid)] = rid
        st["last"] = last
        self._save_state(st)

    def _last_id(self, event):
        sid = self._sender_id(event) or "default"
        val = (self._load_state().get("last") or {}).get(str(sid))
        try:
            return int(val)
        except (TypeError, ValueError):
            return None

    async def _budget_warning(self, month: str, spent: float) -> str:
        """记完一笔后看预算：超过阈值就返回一句提醒。"""
        try:
            budget = await self._call("GET", "/api/budget")
        except (LedgerOffline, LedgerApiError):
            return ""
        if not isinstance(budget, dict):
            return ""
        if month in (budget.get("off") or []):
            return ""
        off_from = str(budget.get("offFrom") or "")
        if off_from and month >= off_from:
            return ""
        raw = budget.get(month) or budget.get("default")
        try:
            limit = float(raw) if raw not in (None, "") else 0.0
        except (TypeError, ValueError):
            return ""
        if limit <= 0:
            return ""
        pct = spent / limit * 100
        try:
            warn_pct = float(self._cfg("budget_warn_pct", 80) or 80)
        except (TypeError, ValueError):
            warn_pct = 80.0
        left = limit - spent
        if left < 0:
            return "注意：本月已超支 %s 元（预算 %s，已用 %.0f%%）" % (money(-left), money(limit), pct)
        if pct >= warn_pct:
            return "提醒：本月预算已用 %.0f%%（%s / %s），还剩 %s 元" % (
                pct, money(spent), money(limit), money(left))
        return ""

    async def _month_spent(self, month: str) -> float:
        try:
            rows = await self._call("GET", "/api/records", params={"month": month})
        except (LedgerOffline, LedgerApiError):
            return 0.0
        total = 0.0
        for r in rows or []:
            if r.get("type") == "income":
                continue
            total += float(r.get("amount") or 0)
        return total

    # ───────────────────────── 安装记账程序 ─────────────────────────
    def _install_app(self, src_hint: str):
        """下载/读取程序包 -> 解压到插件数据目录 -> 找 exe -> 记住路径。"""
        hint = str(src_hint or "").strip().strip('"').strip("'")
        url = hint if hint.lower().startswith(("http://", "https://")) else ""
        local = hint if hint and not url else ""
        if not url and not local:
            url = str(self._cfg("app_url", "") or "").strip()
            local = str(self._cfg("app_zip_path", "") or "").strip()

        if local:
            if not os.path.isfile(local):
                return None, "找不到本地程序包：%s" % local
            with open(local, "rb") as f:
                blob = f.read()
            src_name = local
        elif url:
            if not url.lower().startswith("https://") and "127.0.0.1" not in url and "localhost" not in url:
                return None, "为安全起见只接受 https 下载地址（本机地址除外）。"
            try:
                req = urllib.request.Request(url, headers={"User-Agent": "xiaoai-ledger-plugin"})
                with urllib.request.urlopen(req, timeout=120) as resp:
                    blob = resp.read()
            except Exception as exc:
                return None, "下载失败：%s" % exc
            src_name = url
        else:
            return (None, "还没有程序包地址：请在配置里填 app_url（下载直链），"
                          "或者 /账本安装 <地址|本地zip>")

        if len(blob) < 1024:
            return None, "程序包太小，可能不是有效文件。"
        if len(blob) > 200 * 1024 * 1024:
            return None, "程序包超过 200MB，请检查是否下错。"

        target = os.path.join(os.path.dirname(self._state_file()), "ledger_app")
        os.makedirs(target, exist_ok=True)
        try:
            with zipfile.ZipFile(io.BytesIO(blob)) as z:
                total = 0
                for info in z.infolist():
                    name = info.filename
                    if name.endswith("/"):
                        continue
                    parts = os.path.normpath(name).replace(os.sep, "/").split("/")
                    if ".." in parts or name.startswith("/") or ":" in parts[0]:
                        return None, "程序包里存在可疑路径：%s" % name
                    total += info.file_size
                    if total > 400 * 1024 * 1024:
                        return None, "解压后体积过大，已中止。"
                z.extractall(target)
        except zipfile.BadZipFile:
            return None, "这不是有效的 zip 程序包。"
        except Exception as exc:
            return None, "解压失败：%s" % exc

        exe = ""
        for dirpath, _, names in os.walk(target):
            for n in names:
                if n.lower().endswith(".exe"):
                    exe = os.path.join(dirpath, n)
                    break
            if exe:
                break
        if not exe:
            return None, "程序包里没找到 exe 文件。"

        self._save_state({"exe_path": exe, "source": src_name, "installedAt": int(time.time())})
        return exe, "已安装到：%s" % target

    @filter.command("账本安装")
    async def cmd_install(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        hint = self._payload(event, ("账本安装", "安装"))
        try:
            exe, msg = await asyncio.to_thread(self._install_app, hint)
        except Exception as exc:
            yield event.plain_result("安装出错：%s" % exc)
            return
        if not exe:
            yield event.plain_result(str(msg))
            return
        lines = [str(msg), "程序：%s" % exe]
        cfg_exe = self._exe_path()
        if not cfg_exe:
            lines.append("提示：插件已记住这个路径；想更稳可以在配置里把 exe_path 填成同一个。")
        if bool(self._cfg("auto_start", False)):
            lines.append("auto_start 已开启，下次连不上会自动帮你启动。")
        else:
            lines.append("现在发 /账本状态 前，请先双击那个 exe 打开记账本（或把 auto_start 打开）。")
        yield event.plain_result(NL.join(lines))

    # ───────────────────────── 升级记账本 ─────────────────────────
    def _fetch_zip_bytes(self, hint):
        """按 参数 -> update_url -> update_zip_path 取升级包，返回 (bytes, 来源或错误说明)。"""
        hint = str(hint or "").strip().strip('"').strip("'")
        url_cfg = str(self._cfg("update_url", "") or "").strip()
        path_cfg = str(self._cfg("update_zip_path", "") or "").strip()

        local = ""
        url = ""
        if hint:
            if hint.startswith("http://") or hint.startswith("https://"):
                url = hint
            else:
                local = hint
        if not local and not url:
            local, url = path_cfg, url_cfg
        elif not local and path_cfg and os.path.isfile(path_cfg):
            local = path_cfg
        elif not url and url_cfg:
            url = url_cfg

        if local:
            if not os.path.isfile(local):
                return None, "本地找不到这个文件：%s" % local
            with open(local, "rb") as f:
                return f.read(), local
        if not url:
            return (None, "没有升级包：配置 update_url（下载直链）或 update_zip_path（本地 zip），"
                          "也可以 /账本升级 <地址或路径>")
        req = urllib.request.Request(url, headers={"User-Agent": "xiaoai-ledger-plugin"})
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                return resp.read(), url
        except Exception as exc:
            return None, "下载失败：%s" % exc

    @filter.command("账本升级")
    async def cmd_upgrade(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        hint = self._payload(event, ("账本升级", "升级"))
        try:
            data, src = await asyncio.to_thread(self._fetch_zip_bytes, hint)
        except Exception as exc:
            yield event.plain_result("取升级包出错：%s" % exc)
            return
        if data is None:
            yield event.plain_result(str(src))
            return
        if len(data) > 200 * 1024 * 1024:
            yield event.plain_result("升级包 %.1fMB 超过记账本 200MB 上限，会被拒收。" % (len(data) / 1048576.0))
            return
        try:
            res = await self._call("POST", "/api/upgrade",
                                   {"file": base64.b64encode(data).decode("ascii")})
        except LedgerOffline:
            yield event.plain_result("连不上记账本，先把「小爱记账」打开再来升级。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本拒绝了这次升级：%s" % exc)
            return

        lines = ["升级包已提交（%s，%.1fMB）" % (os.path.basename(str(src)), len(data) / 1048576.0)]
        for key, label in (("updated", "已替换"), ("skipped", "跳过"), ("staged", "待重启生效")):
            vals = res.get(key)
            if isinstance(vals, list) and vals:
                lines.append("%s：%s" % (label, "、".join(str(v) for v in vals)))
        for key, label in (("version", "包内版本"), ("backup", "旧程序备份")):
            if res.get(key):
                lines.append("%s：%s" % (label, res.get(key)))
        if res.get("docsMissing"):
            lines.append("注意：包里缺文档文件（更新日志/手册），版本号是新的但文档没更新。")
        if res.get("downgrade"):
            lines.append("注意：包内版本比当前低（降级），已按你的包执行。")
        if res.get("error"):
            lines.append("错误：%s" % res.get("error"))
        text = NL.join(lines)
        if not any(res.get(k) for k in ("updated", "staged", "error")):
            text += NL + "（记账本返回：" + json.dumps(res, ensure_ascii=False)[:300] + "）"
        text += NL + "exe 需要重启才会换成新版：发 /账本重启（需在配置里打开 allow_restart）。"
        yield event.plain_result(text)

    @filter.command("账本重启")
    async def cmd_restart(self, event: AstrMessageEvent):
        deny = self._denied(event)
        if deny:
            yield event.plain_result(deny)
            return
        if not bool(self._cfg("allow_restart", False)):
            yield event.plain_result(
                "重启开关没打开喵。要在配置里把 allow_restart 设成 true 才允许插件重启记账本。"
            )
            return
        try:
            res = await self._call("GET", "/api/shutdown", params={"relaunch": "1"})
        except LedgerOffline:
            yield event.plain_result("连不上记账本，可能已经在关闭了，等 10 秒发 /账本状态 看看。")
            return
        except LedgerApiError as exc:
            yield event.plain_result("记账本说：%s" % exc)
            return
        yield event.plain_result(
            "已经让记账本重启（relaunch=%s）。等 10～20 秒后发 /账本状态 ，版本号会变成新版。"
            % ("1" if res.get("relaunch") else "0")
        )

    # ───────────────────────── 帮助 ─────────────────────────
    @filter.command("账本")
    async def cmd_help(self, event: AstrMessageEvent):
        yield event.plain_result(HELP_TEXT)
