#!/usr/bin/env python3
"""Local X briefing server. Python standard library only.

    python3 server.py
    open http://127.0.0.1:8787

Accounts are stored in data/accounts.json. Posts are fetched only when the
user clicks 刷新. There is no timer and no polling loop.
"""

from __future__ import annotations

import hashlib
import html
import json
import os
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HOST = "127.0.0.1"
PORT = 8787
POSTS_PER_ACCOUNT = 8
MAX_ACCOUNTS = 20
ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
INDEX = ROOT / "static" / "index.html"
ACCOUNTS_PATH = DATA / "accounts.json"
BRIEFING_PATH = DATA / "briefing.json"
SETTINGS_PATH = DATA / "settings.json"
CACHE_PATH = DATA / "translations.json"

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
)
HANDLE_RE = re.compile(r"^[A-Za-z0-9_]{1,15}$")
NEXT_DATA_RE = re.compile(
    r'<script[^>]*id="__NEXT_DATA__"[^>]*>(.*?)</script>',
    re.DOTALL,
)
CJK_RE = re.compile(r"[\u4e00-\u9fff]")

PROVIDER_LABELS = {
    "syndication": "X 公开嵌入时间线",
    "fxembed": "FxEmbed 公开接口",
    "x-api": "X 官方 API",
}

data_lock = threading.Lock()
refresh_lock = threading.Lock()
refreshing = False
syndication_block_until = 0.0
memory_translations: dict[str, dict] = {}


def browser_persist() -> bool:
    return os.environ.get("VERCEL") == "1"


class AppError(Exception):
    pass


class FetchError(AppError):
    pass


class RateLimitError(FetchError):
    def __init__(self, message: str, reset_at: float | None = None):
        super().__init__(message)
        self.reset_at = reset_at


class TranslationError(AppError):
    pass


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic_write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def read_json(path: Path, default: dict) -> dict:
    if not path.exists():
        return default
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return default
    return data if isinstance(data, dict) else default


def load_accounts() -> list[dict]:
    data = read_json(ACCOUNTS_PATH, {"accounts": []})
    accounts = data.get("accounts") or []
    clean = []
    for item in accounts:
        if isinstance(item, dict) and isinstance(item.get("handle"), str):
            clean.append({"handle": item["handle"], "addedAt": item.get("addedAt") or ""})
    return clean


def load_briefing() -> dict:
    data = read_json(
        BRIEFING_PATH,
        {"refreshedAt": None, "posts": [], "errors": [], "sources": []},
    )
    posts = data.get("posts") if isinstance(data.get("posts"), list) else []
    errors = data.get("errors") if isinstance(data.get("errors"), list) else []
    sources = data.get("sources") if isinstance(data.get("sources"), list) else []
    return {
        "refreshedAt": data.get("refreshedAt"),
        "posts": posts,
        "errors": errors,
        "sources": sources,
    }


def load_token() -> str:
    data = read_json(SETTINGS_PATH, {})
    token = data.get("bearerToken") or ""
    return token.strip() if isinstance(token, str) else ""


def save_token(token: str) -> None:
    if token:
        atomic_write(SETTINGS_PATH, {"bearerToken": token})
        SETTINGS_PATH.chmod(0o600)
    elif SETTINGS_PATH.exists():
        SETTINGS_PATH.unlink()


def normalize_handle(raw: object) -> str:
    if not isinstance(raw, str):
        raise AppError("请输入账号")
    handle = raw.strip().lstrip("@").strip()
    if not HANDLE_RE.fullmatch(handle):
        raise AppError("请输入有效账号：1 到 15 位字母、数字或下划线，可带 @")
    return handle


def parse_time(value: object, timestamp: object = None) -> str | None:
    if isinstance(timestamp, (int, float)) and timestamp > 0:
        seconds = timestamp / 1000 if timestamp >= 1e12 else timestamp
        try:
            return datetime.fromtimestamp(seconds, timezone.utc).isoformat()
        except (OverflowError, OSError, ValueError):
            pass
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip()
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00")).astimezone(timezone.utc).isoformat()
    except ValueError:
        pass
    try:
        return datetime.strptime(text, "%a %b %d %H:%M:%S %z %Y").astimezone(timezone.utc).isoformat()
    except ValueError:
        return None


def safe_x_url(url: object, handle: str, post_id: str) -> str:
    if isinstance(url, str):
        link = url.strip()
        if link.startswith("/"):
            link = "https://x.com" + link
        link = link.replace("https://twitter.com/", "https://x.com/")
        link = link.replace("https://mobile.twitter.com/", "https://x.com/")
        parsed = urllib.parse.urlparse(link)
        if parsed.scheme == "https" and parsed.netloc in {"x.com", "twitter.com", "mobile.twitter.com"}:
            return "https://x.com" + parsed.path
    if post_id and handle:
        return f"https://x.com/{handle}/status/{post_id}"
    return ""


def http_request(url: str, *, method: str = "GET", data: bytes | None = None, headers: dict | None = None, timeout: int = 25):
    req = urllib.request.Request(url, data=data, headers=headers or {}, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as res:
            return res.status, dict(res.headers.items()), res.read()
    except urllib.error.HTTPError as exc:
        return exc.code, dict(exc.headers.items()), exc.read()
    except urllib.error.URLError as exc:
        raise FetchError(f"网络请求失败：{exc.reason}") from exc


def header_get(headers: dict, name: str) -> str:
    for key, value in headers.items():
        if key.lower() == name.lower():
            return str(value)
    return ""


def short_text(value: object, limit: int = 180) -> str:
    text = re.sub(r"\s+", " ", str(value or "")).strip()
    return text[:limit]


def syndication_ready() -> bool:
    return time.time() >= syndication_block_until


def note_syndication_limit(reset_at: float | None) -> None:
    global syndication_block_until
    if reset_at and reset_at > time.time():
        syndication_block_until = reset_at + 1
    else:
        syndication_block_until = time.time() + 15 * 60


def fetch_syndication(handle: str) -> list[dict]:
    url = f"https://syndication.twitter.com/srv/timeline-profile/screen-name/{urllib.parse.quote(handle)}"
    status, headers, body = http_request(
        url,
        headers={"User-Agent": UA, "Accept": "text/html,application/xhtml+xml"},
    )
    text = body.decode("utf-8", "replace")
    remaining = header_get(headers, "x-rate-limit-remaining")
    reset_raw = header_get(headers, "x-rate-limit-reset")
    reset_at = float(reset_raw) if reset_raw.isdigit() else None
    if status == 429 or "Rate limit exceeded" in text:
        note_syndication_limit(reset_at)
        raise RateLimitError("X 公开嵌入时间线正在限流", reset_at)
    if status != 200:
        raise FetchError(f"X 公开嵌入时间线返回 HTTP {status}")
    match = NEXT_DATA_RE.search(text)
    if not match:
        raise FetchError("X 公开嵌入时间线没有返回可解析的帖子")
    try:
        data = json.loads(match.group(1))
    except json.JSONDecodeError as exc:
        raise FetchError("X 公开嵌入时间线的数据无法解析") from exc
    page = ((data.get("props") or {}).get("pageProps") or {}) if isinstance(data, dict) else {}
    timeline = page.get("timeline") or {}
    entries = timeline.get("entries") if isinstance(timeline, dict) else None
    if not isinstance(entries, list):
        raise FetchError("X 公开嵌入时间线没有帖子列表")
    posts = []
    for entry in entries:
        tweet = ((entry or {}).get("content") or {}).get("tweet") if isinstance(entry, dict) else None
        if not isinstance(tweet, dict):
            continue
        pieces = [tweet.get("full_text"), tweet.get("text")]
        original = max((piece for piece in pieces if isinstance(piece, str)), key=len, default="")
        original = html.unescape(original).strip()
        if not original:
            continue
        post_id = str(tweet.get("id_str") or tweet.get("id") or "")
        user = tweet.get("user") if isinstance(tweet.get("user"), dict) else {}
        author = str(user.get("screen_name") or handle)
        reply_to = tweet.get("in_reply_to_screen_name")
        posts.append(
            {
                "id": post_id or hashlib.sha256(original.encode()).hexdigest()[:16],
                "handle": handle,
                "authorHandle": author,
                "authorName": str(user.get("name") or ""),
                "reposted": False,
                "replyTo": reply_to if isinstance(reply_to, str) and reply_to else None,
                "time": parse_time(tweet.get("created_at")),
                "text": original,
                "url": safe_x_url(tweet.get("permalink"), author, post_id),
                "provider": "syndication",
            }
        )
        if len(posts) >= POSTS_PER_ACCOUNT:
            break
    if remaining == "0":
        note_syndication_limit(reset_at)
    return posts


def fetch_fxembed(handle: str) -> list[dict]:
    url = (
        "https://api.fxtwitter.com/2/profile/"
        f"{urllib.parse.quote(handle)}/statuses?count={POSTS_PER_ACCOUNT}"
    )
    status, _headers, body = http_request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    try:
        data = json.loads(body.decode("utf-8", "replace") or "{}")
    except json.JSONDecodeError as exc:
        raise FetchError("FxEmbed 返回的不是 JSON") from exc
    if not isinstance(data, dict):
        raise FetchError("FxEmbed 返回了无法识别的结果")
    code = data.get("code", status)
    if status == 404 or code == 404:
        raise FetchError(f"找不到账号 @{handle}")
    if status != 200 or code not in (200, None):
        message = short_text(data.get("message") or f"HTTP {status}")
        raise FetchError(f"读取 @{handle} 失败：{message}")
    results = data.get("results")
    if not isinstance(results, list):
        raise FetchError("FxEmbed 没有返回帖子列表")
    posts = []
    for item in results:
        if not isinstance(item, dict) or item.get("type") not in (None, "status"):
            continue
        original = item.get("text") if isinstance(item.get("text"), str) else ""
        if not original and isinstance(item.get("raw_text"), dict):
            raw = item["raw_text"].get("text")
            original = raw if isinstance(raw, str) else ""
        original = html.unescape(original).strip()
        if not original:
            continue
        author = item.get("author") if isinstance(item.get("author"), dict) else {}
        author_handle = str(author.get("screen_name") or handle)
        reposted_by = item.get("reposted_by") if isinstance(item.get("reposted_by"), dict) else None
        reply = item.get("replying_to") if isinstance(item.get("replying_to"), dict) else None
        post_id = str(item.get("id") or "")
        posts.append(
            {
                "id": post_id or hashlib.sha256(original.encode()).hexdigest()[:16],
                "handle": handle,
                "authorHandle": author_handle,
                "authorName": str(author.get("name") or ""),
                "reposted": bool(reposted_by),
                "replyTo": reply.get("screen_name") if reply and isinstance(reply.get("screen_name"), str) else None,
                "time": parse_time(item.get("created_at"), item.get("created_timestamp")),
                "text": original,
                "url": safe_x_url(item.get("url"), author_handle, post_id),
                "provider": "fxembed",
            }
        )
    posts.sort(key=lambda post: post.get("time") or "", reverse=True)
    return posts[:POSTS_PER_ACCOUNT]


def api_problem(status: int, data: dict) -> str:
    errors = data.get("errors") if isinstance(data.get("errors"), list) else []
    detail = ""
    if errors and isinstance(errors[0], dict):
        detail = str(errors[0].get("detail") or errors[0].get("message") or errors[0].get("title") or "")
    detail = detail or str(data.get("detail") or data.get("title") or "")
    if status == 401:
        return "Bearer Token 无效或已过期"
    if status == 403:
        return "官方 API 拒绝读取。当前套餐可能没有时间线权限"
    if status == 404:
        return "官方 API 找不到这个账号"
    if status == 429:
        return "官方 API 正在限流"
    return short_text(detail or f"HTTP {status}")


def fetch_official(handle: str, token: str) -> list[dict]:
    headers = {"Authorization": f"Bearer {token}", "User-Agent": UA, "Accept": "application/json"}
    status, _headers, body = http_request(
        f"https://api.x.com/2/users/by/username/{urllib.parse.quote(handle)}?user.fields=name,username",
        headers=headers,
    )
    try:
        data = json.loads(body.decode("utf-8", "replace") or "{}")
    except json.JSONDecodeError as exc:
        raise FetchError("官方 API 返回的不是 JSON") from exc
    if status != 200 or not isinstance(data, dict) or "data" not in data:
        raise FetchError(api_problem(status, data if isinstance(data, dict) else {}))
    user = data["data"]
    user_id = str(user.get("id") or "")
    username = str(user.get("username") or handle)
    name = str(user.get("name") or "")
    if not user_id:
        raise FetchError("官方 API 没有返回用户 id")
    tw_status, _tw_headers, tw_body = http_request(
        "https://api.x.com/2/users/"
        f"{urllib.parse.quote(user_id)}/tweets?max_results=10&tweet.fields=created_at,lang,text",
        headers=headers,
    )
    try:
        tweets = json.loads(tw_body.decode("utf-8", "replace") or "{}")
    except json.JSONDecodeError as exc:
        raise FetchError("官方 API 的帖子数据无法解析") from exc
    if tw_status != 200 or not isinstance(tweets, dict):
        raise FetchError(api_problem(tw_status, tweets if isinstance(tweets, dict) else {}))
    posts = []
    for item in tweets.get("data") or []:
        if not isinstance(item, dict):
            continue
        original = html.unescape(str(item.get("text") or "")).strip()
        if not original:
            continue
        post_id = str(item.get("id") or "")
        posts.append(
            {
                "id": post_id,
                "handle": handle,
                "authorHandle": username,
                "authorName": name,
                "reposted": False,
                "replyTo": None,
                "time": parse_time(item.get("created_at")),
                "text": original,
                "url": safe_x_url("", username, post_id),
                "provider": "x-api",
            }
        )
        if len(posts) >= POSTS_PER_ACCOUNT:
            break
    return posts


def best_failure(failures: list[str]) -> str:
    for item in failures:
        if "找不到账号" in item:
            tail = item.split("：", 1)[-1].strip()
            return tail if tail.startswith("找不到账号") else item
    return "；".join(failures)


def fetch_account(handle: str, token: str) -> tuple[list[dict], str]:
    failures: list[str] = []
    if token:
        try:
            return fetch_official(handle, token), "x-api"
        except FetchError as exc:
            failures.append(f"官方 API：{exc}")
    if syndication_ready():
        try:
            syndicated = fetch_syndication(handle)
            if syndicated:
                return syndicated, "syndication"
            failures.append("公开嵌入时间线没有帖子")
        except RateLimitError as exc:
            failures.append(str(exc))
        except FetchError as exc:
            failures.append(f"公开嵌入时间线：{exc}")
    else:
        failures.append("公开嵌入时间线仍在限流，已跳过")
    try:
        return fetch_fxembed(handle), "fxembed"
    except FetchError as exc:
        failures.append(f"FxEmbed：{exc}")
    detail = best_failure(failures) if failures else "没有可用的读取方式"
    raise FetchError(detail)


def split_text(text: str, size: int) -> list[str]:
    parts: list[str] = []
    start = 0
    length = len(text)
    while start < length:
        end = min(length, start + size)
        if end < length:
            window = text[start:end]
            breaks = [window.rfind("\n"), window.rfind("。"), window.rfind(". "), window.rfind(" ")]
            rel = max(breaks)
            if rel >= size // 2:
                end = start + rel + 1
        parts.append(text[start:end])
        start = end
    return parts


def parse_google(payload: object) -> tuple[str, str]:
    if not isinstance(payload, list) or not payload or not isinstance(payload[0], list):
        raise TranslationError("翻译接口返回了无法识别的结果")
    parts: list[str] = []
    for segment in payload[0]:
        if isinstance(segment, list) and segment and isinstance(segment[0], str):
            parts.append(segment[0])
    translated = "".join(parts).strip()
    if not translated:
        raise TranslationError("翻译接口没有返回译文")
    detected = payload[2] if len(payload) > 2 and isinstance(payload[2], str) else ""
    return translated, detected


def translate_google(text: str) -> tuple[str, str]:
    translated: list[str] = []
    detected = ""
    for chunk in split_text(text, 1800):
        form = urllib.parse.urlencode(
            {"client": "gtx", "sl": "auto", "tl": "zh-CN", "dt": "t", "q": chunk}
        ).encode()
        status, _headers, body = http_request(
            "https://translate.googleapis.com/translate_a/single",
            method="POST",
            data=form,
            headers={"User-Agent": UA, "Content-Type": "application/x-www-form-urlencoded"},
            timeout=20,
        )
        if status != 200:
            raise TranslationError(f"Google 翻译 HTTP {status}")
        try:
            payload = json.loads(body.decode("utf-8", "replace"))
        except json.JSONDecodeError as exc:
            raise TranslationError("Google 翻译返回的不是 JSON") from exc
        piece, lang = parse_google(payload)
        translated.append(piece)
        detected = detected or lang
    return "".join(translated), detected


def mymemory_failed(text: str) -> bool:
    return "MYMEMORY WARNING" in text.upper()


def translate_mymemory(text: str) -> tuple[str, str]:
    parts: list[str] = []
    for chunk in split_text(text, 450):
        query = urllib.parse.urlencode({"q": chunk, "langpair": "en|zh-CN"})
        status, _headers, body = http_request(
            "https://api.mymemory.translated.net/get?" + query,
            headers={"User-Agent": UA, "Accept": "application/json"},
            timeout=20,
        )
        if status != 200:
            raise TranslationError(f"MyMemory HTTP {status}")
        try:
            payload = json.loads(body.decode("utf-8", "replace"))
        except json.JSONDecodeError as exc:
            raise TranslationError("MyMemory 返回的不是 JSON") from exc
        if not isinstance(payload, dict) or payload.get("responseStatus") not in (200, "200"):
            raise TranslationError(short_text(payload.get("responseDetails") if isinstance(payload, dict) else "MyMemory 失败"))
        if payload.get("quotaFinished"):
            raise TranslationError("MyMemory 今日免费额度已用完")
        response = payload.get("responseData") if isinstance(payload.get("responseData"), dict) else {}
        piece = str(response.get("translatedText") or "").strip()
        if not piece or mymemory_failed(piece):
            raise TranslationError("MyMemory 没有返回可用译文")
        parts.append(html.unescape(piece))
    return "".join(parts), "en"


def cache_key(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def translate_text(text: str) -> dict:
    key = cache_key(text)
    if browser_persist():
        cached = memory_translations.get(key)
    else:
        with data_lock:
            cache = read_json(CACHE_PATH, {"items": {}})
            items = cache.get("items") if isinstance(cache.get("items"), dict) else {}
            cached = items.get(key)
    if isinstance(cached, dict) and isinstance(cached.get("translation"), str) and cached["translation"].strip():
        return {
            "translation": cached["translation"],
            "sourceLang": cached.get("sourceLang") or "",
            "engine": cached.get("engine") or "cache",
        }
    error = ""
    try:
        translated, detected = translate_google(text)
        engine = "google"
    except (FetchError, TranslationError) as exc:
        error = str(exc)
        try:
            translated, detected = translate_mymemory(text)
            engine = "mymemory"
        except (FetchError, TranslationError) as second:
            raise TranslationError(f"{error}；MyMemory：{second}") from second
    result = {"translation": translated, "sourceLang": detected, "engine": engine}
    if browser_persist():
        memory_translations[key] = result
        return result
    with data_lock:
        cache = read_json(CACHE_PATH, {"items": {}})
        items = cache.get("items") if isinstance(cache.get("items"), dict) else {}
        items[key] = result
        atomic_write(CACHE_PATH, {"items": items})
    return result


def apply_translation(post: dict) -> dict:
    item = dict(post)
    try:
        result = translate_text(item["text"])
    except TranslationError as exc:
        item["translation"] = None
        item["translationError"] = str(exc)
        item["sourceLang"] = ""
        item["engine"] = ""
    else:
        item["translation"] = result["translation"]
        item["translationError"] = None
        item["sourceLang"] = result["sourceLang"]
        item["engine"] = result["engine"]
    return item


def state_payload(
    accounts: list,
    posts: list,
    errors: list,
    sources: list,
    refreshed_at: str | None,
    token: str,
    active: bool,
) -> dict:
    return {
        "accounts": accounts,
        "posts": posts,
        "errors": errors,
        "sources": sources,
        "refreshedAt": refreshed_at,
        "bearerConfigured": bool(token),
        "refreshing": active,
        "providerLabels": PROVIDER_LABELS,
        "persist": "browser" if browser_persist() else "file",
    }


def public_state() -> dict:
    with data_lock:
        accounts = load_accounts()
        briefing = load_briefing()
        token = load_token()
        active = refreshing
    return state_payload(
        accounts,
        briefing["posts"],
        briefing["errors"],
        briefing["sources"],
        briefing["refreshedAt"],
        token,
        active,
    )


def request_accounts(payload: dict) -> list[dict] | None:
    if "accounts" not in payload:
        return None
    raw = payload.get("accounts")
    if not isinstance(raw, list):
        raise AppError("账号列表格式不正确")
    accounts = []
    seen: set[str] = set()
    for item in raw:
        handle_raw = item.get("handle") if isinstance(item, dict) else item
        added_at = item.get("addedAt") if isinstance(item, dict) and isinstance(item.get("addedAt"), str) else ""
        handle = normalize_handle(handle_raw)
        if handle.lower() in seen:
            continue
        seen.add(handle.lower())
        if len(accounts) >= MAX_ACCOUNTS:
            raise AppError(f"最多添加 {MAX_ACCOUNTS} 个账号")
        accounts.append({"handle": handle, "addedAt": added_at})
    return accounts


def request_token(payload: dict) -> str | None:
    if "bearerToken" not in payload:
        return None
    raw = payload.get("bearerToken")
    if not isinstance(raw, str):
        raise AppError("Bearer Token 必须是文本")
    token = raw.strip()
    if token.lower().startswith("bearer "):
        token = token[7:].strip()
    if len(token) > 400:
        raise AppError("Bearer Token 太长")
    return token


def add_account(raw: object) -> dict:
    handle = normalize_handle(raw)
    with data_lock:
        accounts = load_accounts()
        if any(item["handle"].lower() == handle.lower() for item in accounts):
            raise AppError("这个账号已经在列表里")
        if len(accounts) >= MAX_ACCOUNTS:
            raise AppError(f"最多添加 {MAX_ACCOUNTS} 个账号")
        accounts.append({"handle": handle, "addedAt": now_iso()})
        atomic_write(ACCOUNTS_PATH, {"accounts": accounts})
    return public_state()


def delete_account(raw: object) -> dict:
    handle = normalize_handle(raw)
    with data_lock:
        accounts = load_accounts()
        kept = [item for item in accounts if item["handle"].lower() != handle.lower()]
        if len(kept) == len(accounts):
            raise AppError("列表里没有这个账号")
        atomic_write(ACCOUNTS_PATH, {"accounts": kept})
        briefing = load_briefing()
        posts = [post for post in briefing["posts"] if str(post.get("handle", "")).lower() != handle.lower()]
        errors = [item for item in briefing["errors"] if str(item.get("handle", "")).lower() != handle.lower()]
        sources = [item for item in briefing["sources"] if str(item.get("handle", "")).lower() != handle.lower()]
        if not kept:
            posts, errors, sources = [], [], []
        atomic_write(
            BRIEFING_PATH,
            {
                "refreshedAt": briefing["refreshedAt"] if kept else None,
                "posts": posts,
                "errors": errors,
                "sources": sources,
            },
        )
    return public_state()


def refresh_accounts(payload: dict | None = None) -> dict:
    global refreshing
    payload = payload or {}
    if not refresh_lock.acquire(blocking=False):
        raise AppError("正在刷新，请稍候")
    try:
        refreshing = True
        supplied = request_accounts(payload)
        supplied_token = request_token(payload)
        ephemeral = supplied is not None
        with data_lock:
            accounts = supplied if supplied is not None else load_accounts()
            token = supplied_token if supplied_token is not None else load_token()
            previous_briefing = {"posts": [], "errors": [], "sources": []} if ephemeral else load_briefing()
        previous = previous_briefing["posts"]
        previous_sources = previous_briefing["sources"]
        if not accounts:
            raise AppError("还没有账号。请先添加一个 X 账号")
        posts = list(previous)
        errors = []
        sources = []
        for account in accounts:
            handle = account["handle"]
            try:
                fetched, provider = fetch_account(handle, token)
            except FetchError as exc:
                errors.append({"handle": handle, "message": str(exc)})
                old_source = next(
                    (item for item in previous_sources if str(item.get("handle", "")).lower() == handle.lower()),
                    None,
                )
                if old_source:
                    sources.append(old_source)
                print(f"refresh @{handle} failed: {exc}", flush=True)
                continue
            workers = min(6, max(1, len(fetched)))
            with ThreadPoolExecutor(max_workers=workers) as pool:
                translated_posts = list(pool.map(apply_translation, fetched))
            posts = [post for post in posts if str(post.get("handle", "")).lower() != handle.lower()]
            posts.extend(translated_posts)
            sources.append({"handle": handle, "provider": provider, "count": len(translated_posts)})
            if not translated_posts:
                errors.append({"handle": handle, "message": "没有读到公开帖子"})
            print(f"refresh @{handle}: {len(translated_posts)} posts via {provider}", flush=True)
        if ephemeral:
            current = {item["handle"].lower() for item in accounts}
        else:
            with data_lock:
                current = {item["handle"].lower() for item in load_accounts()}
        posts = [post for post in posts if str(post.get("handle", "")).lower() in current]
        errors = [item for item in errors if str(item.get("handle", "")).lower() in current]
        sources = [item for item in sources if str(item.get("handle", "")).lower() in current]
        posts.sort(key=lambda post: post.get("time") or "", reverse=True)
        refreshed_at = now_iso()
        if ephemeral:
            return state_payload(accounts, posts, errors, sources, refreshed_at, token, False)
        with data_lock:
            atomic_write(
                BRIEFING_PATH,
                {"refreshedAt": refreshed_at, "posts": posts, "errors": errors, "sources": sources},
            )
        return public_state()
    finally:
        refreshing = False
        refresh_lock.release()


def update_settings(payload: dict) -> dict:
    if "bearerToken" not in payload:
        raise AppError("缺少 bearerToken")
    raw = payload.get("bearerToken")
    if raw is None:
        raw = ""
    if not isinstance(raw, str):
        raise AppError("Bearer Token 必须是文本")
    token = raw.strip()
    if token.lower().startswith("bearer "):
        token = token[7:].strip()
    if token and len(token) > 400:
        raise AppError("Bearer Token 太长")
    with data_lock:
        save_token(token)
    return public_state()


class Handler(BaseHTTPRequestHandler):
    server_version = "XBriefing/1.0"

    def log_message(self, fmt: str, *args) -> None:
        sys.stderr.write("%s - %s\n" % (self.log_date_time_string(), fmt % args))

    def route_path(self) -> str:
        forced = getattr(self, "vercel_path", None)
        if isinstance(forced, str) and forced:
            return forced
        forwarded = self.headers.get("x-forwarded-uri") or self.headers.get("x-invoke-path") or self.path
        return urllib.parse.urlparse(forwarded).path

    def do_GET(self) -> None:
        path = self.route_path()
        if path in ("/", "/index.html"):
            self.send_file(INDEX, "text/html; charset=utf-8")
            return
        if path == "/favicon.ico":
            self.send_bytes(204, b"", "image/x-icon")
            return
        if path == "/api/state":
            self.send_json(200, public_state())
            return
        self.send_json(404, {"error": "没有这个地址"})

    def do_POST(self) -> None:
        path = self.route_path()
        try:
            if path == "/api/accounts":
                self.send_json(200, add_account(self.read_body().get("handle")))
                return
            if path == "/api/refresh":
                self.send_json(200, refresh_accounts(self.read_body()))
                return
        except AppError as exc:
            status = 409 if "已经" in str(exc) or "正在刷新" in str(exc) else 400
            self.send_json(status, {"error": str(exc)})
            return
        self.send_json(404, {"error": "没有这个地址"})

    def do_DELETE(self) -> None:
        path = self.route_path()
        prefix = "/api/accounts/"
        if not path.startswith(prefix):
            self.send_json(404, {"error": "没有这个地址"})
            return
        try:
            handle = urllib.parse.unquote(path[len(prefix) :])
            self.send_json(200, delete_account(handle))
        except AppError as exc:
            status = 404 if "没有这个账号" in str(exc) else 400
            self.send_json(status, {"error": str(exc)})

    def do_PUT(self) -> None:
        path = self.route_path()
        if path != "/api/settings":
            self.send_json(404, {"error": "没有这个地址"})
            return
        try:
            self.send_json(200, update_settings(self.read_body()))
        except AppError as exc:
            self.send_json(400, {"error": str(exc)})

    def read_body(self) -> dict:
        length = int(self.headers.get("Content-Length") or 0)
        if length > 16_000:
            raise AppError("请求太大")
        raw = self.rfile.read(length) if length else b""
        if not raw:
            return {}
        try:
            data = json.loads(raw.decode("utf-8"))
        except json.JSONDecodeError as exc:
            raise AppError("请求不是 JSON") from exc
        if not isinstance(data, dict):
            raise AppError("请求格式不正确")
        return data

    def send_file(self, path: Path, content_type: str) -> None:
        if not path.exists():
            self.send_json(500, {"error": "页面文件缺失"})
            return
        self.send_bytes(200, path.read_bytes(), content_type)

    def send_json(self, status: int, payload: dict) -> None:
        self.send_bytes(status, json.dumps(payload, ensure_ascii=False).encode("utf-8"), "application/json; charset=utf-8")

    def send_bytes(self, status: int, body: bytes, content_type: str) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)


def self_check() -> None:
    assert normalize_handle(" @Ab_c ") == "Ab_c"
    try:
        normalize_handle("not a handle")
    except AppError:
        pass
    else:
        raise AssertionError("invalid handle was accepted")
    fixture = """
    <script id="__NEXT_DATA__" type="application/json">
    {"props":{"pageProps":{"timeline":{"entries":[
      {"content":{"tweet":{
        "id_str":"99",
        "full_text":"Hello &amp; welcome",
        "created_at":"Mon Oct 26 19:29:09 +0000 2026",
        "permalink":"/example/status/99",
        "user":{"screen_name":"example","name":"Example"}
      }}}
    ]}}}}
    </script>
    """
    posts = parse_syndication_html(fixture, "example")
    assert posts[0]["text"] == "Hello & welcome"
    assert posts[0]["url"] == "https://x.com/example/status/99"
    assert posts[0]["time"].startswith("2026-10-26T19:29:09")
    translated, lang = parse_google([[["今晚卫星将飞越太平洋。", "source", None]], None, "en"])
    assert "卫星" in translated and lang == "en"
    assert mymemory_failed("MYMEMORY WARNING: YOU USED ALL AVAILABLE FREE TRANSLATIONS")
    fx_posts = posts_from_fx(
        {
            "code": 200,
            "results": [
                {
                    "type": "status",
                    "id": "7",
                    "text": "A public post",
                    "created_timestamp": 1793389772,
                    "url": "https://twitter.com/example/status/7",
                    "author": {"screen_name": "example", "name": "Example"},
                    "reposted_by": None,
                    "replying_to": None,
                }
            ],
        },
        "example",
    )
    assert fx_posts[0]["url"] == "https://x.com/example/status/7"
    assert fx_posts[0]["text"] == "A public post"
    print("self-check ok")


def parse_syndication_html(page: str, handle: str) -> list[dict]:
    match = NEXT_DATA_RE.search(page)
    if not match:
        raise FetchError("missing next data")
    data = json.loads(match.group(1))
    entries = data["props"]["pageProps"]["timeline"]["entries"]
    posts = []
    for entry in entries:
        tweet = entry["content"]["tweet"]
        original = html.unescape(tweet.get("full_text") or tweet.get("text") or "").strip()
        post_id = str(tweet.get("id_str") or "")
        author = tweet["user"]["screen_name"]
        posts.append(
            {
                "text": original,
                "url": safe_x_url(tweet.get("permalink"), author, post_id),
                "time": parse_time(tweet.get("created_at")),
            }
        )
    return posts


def posts_from_fx(data: dict, handle: str) -> list[dict]:
    if data.get("code") == 404:
        raise FetchError(f"找不到账号 @{handle}")
    posts = []
    for item in data.get("results") or []:
        posts.append(
            {
                "text": item.get("text") or "",
                "url": safe_x_url(item.get("url"), handle, str(item.get("id") or "")),
            }
        )
    return posts


def main() -> None:
    if "--self-check" in sys.argv:
        self_check()
        return
    DATA.mkdir(parents=True, exist_ok=True)
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    server.daemon_threads = True
    print(f"X briefing listening on http://{HOST}:{PORT}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nstopped", flush=True)


if __name__ == "__main__":
    main()
