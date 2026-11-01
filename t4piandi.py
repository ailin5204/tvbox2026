# -*- coding: utf-8 -*-
# 懂片帝 - TVBox / 追剧影视 通用 Python 爬虫
# 站点：https://dongpian17.com
# 接口：/v1/* REST API（HMAC-SHA256 请求签名，换行分隔）
# 分类：大家都在看（全部/电影/剧集/短剧/动漫/综艺 × 日榜/周榜/月榜/总榜）
# 检修说明：原稿逻辑与结构就地保留（签名机制、榜单分类体系、官方线路过滤、4K 置顶、
# 匿名游客会话、resolve-line 二次解析均未改）；只修 Jython 2.7 加载死与 T4 归一问题。
# 卡图：正常卡图，本版不加 style 大图字段（用户本次只说检修、未说大图）。
import sys
import json
import time
import hmac
import hashlib
import os
import re

try:
    import binascii as _binascii
except Exception:
    _binascii = None

# ↓↓↓ TVBox Python 插件：base 包在上一级目录 ↓↓↓
try:
    sys.path.append('..')
except Exception:
    pass

try:
    from base.spider import Spider as BaseSpider
except Exception:
    BaseSpider = None

# requests 在盒端常缺失：可选导入，不可用时走 urllib 回退，顶层绝不裸跑
try:
    import requests as _requests
except Exception:
    _requests = None

if _requests is not None:
    try:
        _requests.packages.urllib3.disable_warnings()
    except Exception:
        pass

# urllib 双回退（py3 urllib.request / py2 urllib2）
try:
    import urllib.request as _urlreq
    import urllib.error as _urlerr
except Exception:
    import urllib2 as _urlreq
    import urllib2 as _urlerr

try:
    import ssl as _ssl
except Exception:
    _ssl = None

try:
    import gzip as _gzip
except Exception:
    _gzip = None

try:
    _STR = basestring
except Exception:
    _STR = str


def _txt(x):
    """外部文本安全转 unicode/str：py2 下含中文 unicode 裸 str() 会报编码错。"""
    if x is None:
        return u""
    # py3 下 bytes 绝不能走 str()（会变成 "b'...'" 字面量，签名 nonce 即因此被拒）
    if isinstance(x, bytes):
        try:
            return x.decode("utf-8")
        except Exception:
            return x.decode("utf-8", "replace")
    if isinstance(x, _STR):
        return x
    try:
        return unicode(x)
    except Exception:
        pass
    try:
        return str(x)
    except Exception:
        return u""


def _is_str(x):
    return isinstance(x, _STR)


def _nonce_hex():
    """py2 下 bytes 没有 .hex()，用 binascii 兼容。"""
    raw = os.urandom(16)
    if _binascii is not None:
        try:
            h = _binascii.hexlify(raw)
            return _txt(h)
        except Exception:
            pass
    try:
        return raw.encode("hex")
    except Exception:
        return u"".join(u"%02x" % ord(c) for c in _txt(raw))


def _quote(s):
    """py2 urllib.quote 不接受 unicode：先转 utf-8 字节再 quote。"""
    t = _txt(s)
    try:
        from urllib.parse import quote as _q
        return _q(t)
    except Exception:
        pass
    try:
        import urllib as _u
        return _u.quote(t.encode("utf-8"))
    except Exception:
        return t


# ---------- 简介清洗：先 strip 标签，再单次 unescape，禁止双重解码 ----------
_ENTITY_MAP = {
    "amp": u"&", "lt": u"<", "gt": u">", "quot": u'"', "apos": u"'",
    "nbsp": u" ", "ldquo": u"\u201c", "rdquo": u"\u201d",
    "lsquo": u"\u2018", "rsquo": u"\u2019", "hellip": u"\u2026",
    "mdash": u"\u2014", "ndash": u"\u2013", "middot": u"\u00b7",
}


def _unescape_once(s):
    def _rep(m):
        body = m.group(1)
        if body.startswith("#"):
            try:
                if body[1] in ("x", "X"):
                    return unichr(int(body[2:], 16))
                return unichr(int(body[1:]))
            except Exception:
                return m.group(0)
        return _ENTITY_MAP.get(body, m.group(0))
    try:
        return re.sub(u"&(#x?[0-9a-fA-F]+|[a-zA-Z]+);", _rep, s)
    except Exception:
        try:
            return re.sub(r"&(#x?[0-9a-fA-F]+|[a-zA-Z]+);", _rep, s)
        except Exception:
            return s


def _clean_text(s):
    t = _txt(s or u"")
    try:
        t = re.sub(u"<[^>]+>", u"", t)
    except Exception:
        t = re.sub(r"<[^>]+>", u"", t)
    t = _unescape_once(t)
    return t.strip()


def _tag(name):
    n = _txt(name or u"").strip()
    if not n:
        return u""
    return u'[a=cr:{"name":"' + n + u'"/}]' + n + u"[/a]"


def _tags(names):
    out = []
    for n in (names or []):
        t = _tag(n)
        if t:
            out.append(t)
    return u" ".join(out)


try:
    unicode
    _PY2 = True
except Exception:
    _PY2 = False


def _log(msg):
    """py2 下含中文 unicode 直接 print(字节串格式) 会报 ascii 编码错，统一走这里。"""
    try:
        t = _txt(msg)
        if _PY2:
            t = t.encode("utf-8")
        sys.stdout.write(t + "\n")
    except Exception:
        pass


class _Resp(object):
    def __init__(self, text, status_code):
        self.text = text
        self.status_code = status_code
        try:
            self.content = text.encode("utf-8")
        except Exception:
            self.content = b""


class _CookieJar(object):
    def __init__(self):
        self._d = {}

    def set(self, k, v, domain=None, path="/"):
        try:
            self._d[_txt(k).strip()] = _txt(v).strip()
        except Exception:
            pass

    def header(self):
        try:
            return "; ".join(u"{}={}".format(k, v) for k, v in self._d.items())
        except Exception:
            return u""

    def update_from(self, headers):
        try:
            vals = []
            if hasattr(headers, "get_all"):
                vals = headers.get_all("Set-Cookie") or []
            elif hasattr(headers, "getheaders"):
                vals = headers.getheaders("Set-Cookie") or []
            for sc in vals:
                first = _txt(sc).split(";")[0].strip()
                if "=" in first:
                    k, v = first.split("=", 1)
                    self.set(k, v)
        except Exception:
            pass


class _UrllibSession(object):
    """requests 不可用时的 urllib 回退会话：只实现脚本用到的 get/post/cookies。"""

    def __init__(self):
        self.cookies = _CookieJar()
        self._ctx = None
        if _ssl is not None:
            try:
                self._ctx = _ssl._create_unverified_context()
            except Exception:
                self._ctx = None

    def _request(self, method, url, headers=None, data=None, timeout=12):
        hdrs = {}
        for k, v in (headers or {}).items():
            hdrs[_txt(k)] = _txt(v)
        ck = self.cookies.header()
        if ck:
            hdrs["Cookie"] = ck
        body = None
        if data is not None:
            if isinstance(data, _STR):
                body = _txt(data).encode("utf-8")
            else:
                body = data
        req = _urlreq.Request(url, data=body, headers=hdrs)
        try:
            req.get_method = lambda: method
        except Exception:
            pass
        try:
            if isinstance(timeout, (tuple, list)):
                timeout = timeout[1] if len(timeout) > 1 else timeout[0]
        except Exception:
            pass
        try:
            if self._ctx is not None:
                opener = _urlreq.build_opener(_urlreq.HTTPSHandler(context=self._ctx))
            else:
                opener = _urlreq.build_opener()
        except Exception:
            opener = _urlreq.build_opener()
        try:
            resp = opener.open(req, timeout=timeout)
            raw = resp.read()
            try:
                self.cookies.update_from(resp.info())
            except Exception:
                pass
            return _Resp(self._decode(raw, resp), resp.getcode())
        except _urlerr.HTTPError as e:
            try:
                raw = e.read()
            except Exception:
                raw = b""
            try:
                self.cookies.update_from(e.info())
            except Exception:
                pass
            return _Resp(self._decode(raw, e), e.code)

    def _decode(self, raw, resp):
        try:
            enc = ""
            try:
                enc = _txt(resp.info().get("Content-Encoding") or "")
            except Exception:
                pass
            if (enc and "gzip" in enc.lower()) or (len(raw) >= 2 and raw[0] == 0x1f and raw[1] == 0x8b):
                if _gzip is not None:
                    try:
                        import io as _io
                        raw = _gzip.GzipFile(fileobj=_io.BytesIO(raw)).read()
                    except Exception:
                        pass
            if isinstance(raw, bytes):
                return raw.decode("utf-8", "replace")
            return _txt(raw)
        except Exception:
            return u""

    def get(self, url, headers=None, timeout=12, verify=False, **kwargs):
        return self._request("GET", url, headers=headers, timeout=timeout)

    def post(self, url, headers=None, json=None, data=None, timeout=12, verify=False, **kwargs):
        hdrs = dict(headers or {})
        body = data
        if json is not None:
            body = json.dumps(json, ensure_ascii=False)
            hdrs.setdefault("Content-Type", "application/json")
        return self._request("POST", url, headers=hdrs, data=body, timeout=timeout)


def _make_session():
    if _requests is not None:
        try:
            return _requests.Session()
        except Exception:
            pass
    return _UrllibSession()


if BaseSpider is None:
    class BaseSpider(object):
        def __init__(self):
            self.extend = ''

        def init(self, extend=""):
            pass

        def getName(self):
            return ""

        def isVideoFormat(self, url):
            return False

        def manualVideoCheck(self):
            return False

        def destroy(self):
            pass

        def localProxy(self, param):
            return [404, "text/plain", b""]

        def fetch(self, url, params=None, headers=None, cookies=None,
                  timeout=15, verify=False, encoding="utf-8", **kwargs):
            sess = _make_session()
            resp = sess.get(url, headers=headers, timeout=timeout, verify=verify)
            return _Resp(resp.text, resp.status_code)


class Spider(BaseSpider):

    # 请求签名密钥（硬编码于前端 movie-card-runtime，HMAC-SHA256，消息为 方法\n路径+查询\n时间戳\n随机数）
    SIGN_KEY = "8b9a908a05eac640e1ee06f52acaa741bfe4ba9e004eeffdbeb635e532e06666"

    # 分类映射：tab名 → kind 参数
    KINDS = [
        ("all", "全部"),
        ("movie", "电影"),
        ("series", "剧集"),
        ("short_drama", "短剧"),
        ("anime", "动漫"),
        ("variety", "综艺"),
    ]

    # 榜单映射
    WINDOWS = [
        ("day", "日榜"),
        ("week", "周榜"),
        ("month", "月榜"),
        ("total", "总榜"),
    ]

    def __init__(self):
        try:
            super(Spider, self).__init__()
        except Exception:
            pass
        self.host = "https://dongpian17.com"
        self.name = "懂片帝"
        self.ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36"
        self.session = _make_session()
        self.account = ""
        self.password = ""
        self.cookie_str = ""
        self._logged_in = False
        self._home_cache = None
        self._home_cache_ts = 0

    def init(self, extend=""):
        try:
            super(Spider, self).init(extend)
        except Exception:
            pass
        try:
            if not extend:
                extend = getattr(self, 'extend', '')
            if _is_str(extend):
                try:
                    ext = json.loads(extend) if extend.strip() else {}
                except Exception:
                    ext = {}
            elif isinstance(extend, dict):
                ext = extend
            else:
                ext = {}
            self.host = _txt(ext.get("host", self.host)).rstrip("/")
            self.name = _txt(ext.get("name", self.name))
            self.ua = _txt(ext.get("ua", self.ua))
            # 账号配置：官方线路需登录播放，支持 account/password 或直接给 cookie
            self.account = _txt(ext.get("account", self.account))
            self.password = _txt(ext.get("password", self.password))
            self.cookie_str = _txt(ext.get("cookie", self.cookie_str))
            if self.cookie_str:
                self._apply_cookie(self.cookie_str)
                self._logged_in = True
            _log(u"懂片帝 init: host={}, name={}".format(self.host, self.name))
        except Exception as e:
            _log(u"懂片帝 init error: {}".format(e))

    # ================= 登录会话 =================

    def _apply_cookie(self, cookie_str):
        try:
            for kv in _txt(cookie_str).split(";"):
                kv = kv.strip()
                if "=" in kv:
                    k, v = kv.split("=", 1)
                    self.session.cookies.set(k.strip(), v.strip())
        except Exception as e:
            _log(u"懂片帝 apply cookie error: {}".format(e))

    def _login(self):
        """账号密码登录，成功后会话cookie保存在 session 中"""
        if not self.account or not self.password:
            return False
        try:
            path = "/v1/users/password/login"
            headers = self._headers("POST", path, "")
            headers["Content-Type"] = "application/json"
            resp = self.session.post(self.host + path, headers=headers,
                                     json={"account": self.account, "password": self.password},
                                     timeout=(8, 12), verify=False)
            data = json.loads(resp.text)
            if resp.status_code == 200 and not data.get("error"):
                self._logged_in = True
                _log(u"懂片帝 login ok: {}".format(self.account))
                return True
            _log(u"懂片帝 login fail: {}".format(resp.text[:200]))
        except Exception as e:
            _log(u"懂片帝 login error: {}".format(e))
        return False

    def _anonymous_login(self):
        """注册匿名(游客)会话：POST /v1/users/anonymous，服务端种 ai_movie_session cookie。
        官方线路按游客账号配额计费，有游客会话即可免登录播放。"""
        try:
            import uuid
            path = "/v1/users/anonymous"
            headers = self._headers("POST", path, "")
            headers["Content-Type"] = "application/json"
            anon_id = u"web_{}".format(uuid.uuid4())
            resp = self.session.post(self.host + path, headers=headers,
                                     json={"anonymous_id": anon_id},
                                     timeout=(8, 12), verify=False)
            if resp.status_code in (200, 201):
                self._logged_in = True
                _log(u"懂片帝 anonymous session ok: {}".format(anon_id))
                return True
            _log(u"懂片帝 anonymous fail: {} {}".format(resp.status_code, resp.text[:200]))
        except Exception as e:
            _log(u"懂片帝 anonymous error: {}".format(e))
        return False

    def _ensure_login(self):
        if self._logged_in:
            return True
        # 优先账号密码登录（配额更高），否则注册匿名游客会话
        if self.account and self.password:
            return self._login()
        return self._anonymous_login()

    # ================= 签名请求 =================

    def _headers(self, method, path, search):
        ts = str(int(time.time() * 1000))
        nonce = _nonce_hex()
        msg = u"{}\n{}{}\n{}\n{}".format(method, path, search, ts, nonce)
        sign = hmac.new(self.SIGN_KEY.encode(), msg.encode(), hashlib.sha256).hexdigest()
        return {
            "User-Agent": self.ua,
            "Accept": "application/json",
            "x-ai-movie-client-name": "movie-search-frontend",
            "x-ai-movie-client-version": "1.0.0",
            "x-ai-movie-build-version": "dongpiandi-v2026.10.04.1-episode-resume-efd9a7f2e87e-web",
            "x-ai-movie-protocol-version": "2026-07-05.library-v2.playback-v1",
            "x-ai-movie-timestamp": ts,
            "x-ai-movie-nonce": nonce,
            "x-ai-movie-signature": sign,
        }

    def _get(self, path, search=""):
        try:
            resp = self.session.get(self.host + path + search,
                                    headers=self._headers("GET", path, search),
                                    timeout=(8, 12), verify=False)
            data = json.loads(resp.text)
            if isinstance(data, dict):
                return data
            return {}
        except Exception as e:
            _log(u"懂片帝 _get error {}: {}".format(path, e))
            return {}

    def _post(self, path, search, body):
        try:
            headers = self._headers("POST", path, search)
            headers["Content-Type"] = "application/json"
            resp = self.session.post(self.host + path + search, headers=headers,
                                     json=body, timeout=(8, 12), verify=False)
            data = json.loads(resp.text)
            if isinstance(data, dict):
                return data
            return {}
        except Exception as e:
            _log(u"懂片帝 _post error {}: {}".format(path, e))
            return {}

    def _resolve_line(self, ticket, retried=False):
        """resolve-line 二次解析，遇登录要求时自动登录重试一次"""
        d2 = self._post("/v1/playback/resolve-line", "?view=compact", {"ticket": ticket})
        if d2.get("code") == "playback_user_session_required" and not retried:
            if self._ensure_login():
                d2 = self._post("/v1/playback/resolve-line", "?view=compact", {"ticket": ticket})
        return d2.get("line", {}) or {}

    # ================= TVBox 接口 =================

    def _home_videos(self):
        # 首页推荐缓存 60 秒：homeContent 与 homeVideoContent 同一轮只拉一次
        try:
            now = time.time()
            if self._home_cache is not None and now - self._home_cache_ts < 60:
                return list(self._home_cache)
        except Exception:
            pass
        data = self._get("/v1/feed/home", "?scope=public&mode=preview&sections=3&cards=12")
        videos = []
        for sec in data.get("sections", []):
            if sec.get("id") == "feed_sec_everyone_watching" or sec.get("type") == "trend":
                for card in sec.get("cards", []):
                    videos.append(self._parse_card(card))
                break
        if not videos:
            for sec in data.get("sections", []):
                for card in sec.get("cards", []):
                    videos.append(self._parse_card(card))
                if videos:
                    break
        try:
            self._home_cache = list(videos)
            self._home_cache_ts = time.time()
        except Exception:
            pass
        return videos

    def homeContent(self, filter):
        classes = []
        for tid, tname in self.KINDS:
            classes.append({"type_id": tid, "type_name": tname})

        filters = {}
        if filter:
            window_values = [{"n": n, "v": v} for v, n in self.WINDOWS]
            for tid, _ in self.KINDS:
                filters[tid] = [{
                    "key": "window",
                    "name": "榜单",
                    "value": window_values,
                }]
        # T4 要求 homeContent 必须带 list，否则壳子首页显示“加载不出来”
        try:
            videos = self._home_videos()
        except Exception:
            videos = []
        return {"class": classes, "filters": filters, "list": videos}

    def homeVideoContent(self):
        # 首页推荐：大家都在看（日榜快照）
        try:
            videos = self._home_videos()
        except Exception:
            videos = []
        return {"list": videos}

    def categoryContent(self, tid, pg, filter, extend):
        window = "day"
        if extend and extend.get("window"):
            window = extend["window"]

        search = u"?sort=trending&window={}&page={}&limit=20".format(window, pg)
        if tid and tid != "all":
            search += "&kind=" + tid

        data = self._get("/v1/browse/catalog", search)

        videos = []
        for card in data.get("cards", []):
            videos.append(self._parse_card(card))

        pagination = data.get("pagination", {}) or {}
        has_more = bool(pagination.get("has_more"))
        try:
            page = int(pg)
        except Exception:
            page = 1
        pagecount = page + 1 if has_more else page

        return {
            "page": page,
            "pagecount": pagecount,
            "limit": 20,
            "total": pagecount * 20,
            "list": videos,
        }

    def _chunk_play(self, entries, limit=1900):
        """多集按 ≤1900 字节分段，防 vod_play_url 整串截断丢尾集。"""
        chunks = []
        cur = []
        cur_len = 0
        for e in entries:
            elen = len(e.encode("utf-8")) if isinstance(e, str) else len(_txt(e).encode("utf-8"))
            add = elen + (1 if cur else 0)
            if cur and cur_len + add > limit:
                chunks.append("#".join(cur))
                cur = [e]
                cur_len = elen
            else:
                cur.append(e)
                cur_len += add
        if cur:
            chunks.append("#".join(cur))
        return chunks

    def detailContent(self, ids):
        vid = ids[0] if isinstance(ids, list) else ids
        data = self._get("/v1/catalog/" + _txt(vid))
        card = data.get("card", data) if isinstance(data, dict) else {}

        episodes = card.get("episodes") or []
        # 详情内嵌剧集不全时，走剧集分页接口补齐
        episode_count = card.get("episode_count") or len(episodes)
        if episode_count > len(episodes):
            episodes = self._fetch_all_episodes(vid, episodes)

        play_urls = []
        for ep in episodes:
            title = ep.get("title") or ep.get("display_name") or u"第{}集".format(ep.get("number", ""))
            token = ep.get("token", "")
            if token:
                play_urls.append(u"{}${}".format(_txt(title), token))

        vod = self._parse_card(card)
        vod["vod_id"] = _txt(vid)

        # 用第1集 token 拉取线路列表，把官方线路写到播放来源，可切换播放
        lines = []
        if episodes:
            first_token = episodes[0].get("token", "")
            if first_token:
                rdata = self._get("/v1/playback/resolve/" + first_token, "?view=compact")
                lines = rdata.get("line_options", []) or []
        # 只保留官方线路，屏蔽普通资源站线路
        lines = [ln for ln in lines if self._is_official_line(ln)]
        # 4K线路排到最前面（稳定排序，其余保持接口返回顺序）
        lines.sort(key=lambda ln: 0 if "4K" in (_txt(ln.get("label") or "").upper()) else 1)

        if lines and play_urls:
            froms = []
            urls_per_line = []
            used_names = {}
            for ln in lines:
                line_id = ln.get("id", "")
                if not line_id:
                    continue
                label = ln.get("label") or ln.get("play_from") or ln.get("provider_id") or "线路"
                label = self._short_line_name(_txt(label))
                # 同名线路去重（加序号）；同一线路的分段则共用原名
                if label in used_names:
                    used_names[label] += 1
                    disp = u"{}{}".format(label, used_names[label])
                else:
                    used_names[label] = 1
                    disp = label
                eps_urls = []
                for pu in play_urls:
                    title, token = pu.split("$", 1)
                    eps_urls.append(u"{}${}@@{}".format(title, token, line_id))
                for chunk in self._chunk_play(eps_urls):
                    froms.append(disp)
                    urls_per_line.append(chunk)
            if froms:
                vod["vod_play_from"] = "$$$".join(froms)
                vod["vod_play_url"] = "$$$".join(urls_per_line)
            else:
                vod["vod_play_from"] = self.name
                vod["vod_play_url"] = "$$$".join(self._chunk_play(play_urls))
        else:
            vod["vod_play_from"] = self.name
            vod["vod_play_url"] = "$$$".join(self._chunk_play(play_urls)) if play_urls else ""
        return {"list": [vod]}

    def searchContent(self, key, quick):
        q = _quote(key)
        data = self._get("/v1/browse/catalog", u"?q={}&page=1&limit=20".format(q))
        videos = []
        for card in data.get("cards", []):
            videos.append(self._parse_card(card))
        pagination = data.get("pagination", {}) or {}
        has_more = bool(pagination.get("has_more"))
        return {
            "page": 1,
            "pagecount": 2 if has_more else 1,
            "limit": 20,
            "total": len(videos),
            "list": videos,
        }

    def playerContent(self, flag, id, vipFlags):
        token = id
        line_id = ""
        # 详情页写入的格式：token@@线路ID（用于切换播放来源）
        if "@@" in _txt(id):
            token, line_id = _txt(id).split("@@", 1)

        data = self._get("/v1/playback/resolve/" + token, "?view=compact")
        lines = data.get("line_options", []) or []

        play_url = ""
        url_kind = ""

        # 指定线路：按 line_id（或 flag 匹配 label）精确选中
        target = None
        if line_id:
            for ln in lines:
                if ln.get("id") == line_id:
                    target = ln
                    break
        if target is None and flag and flag != self.name:
            for ln in lines:
                if (_txt(ln.get("label") or "") == flag) or (_txt(ln.get("play_from") or "") == flag) \
                        or self._short_line_name(_txt(ln.get("label") or "")) == flag:
                    target = ln
                    break

        if target is not None:
            if target.get("url_kind") == "m3u8" and not target.get("resolve_required") and target.get("url"):
                play_url = target["url"]
                url_kind = "m3u8"
            else:
                ticket = (_txt(target.get("url") or "")).replace("resolve://", "")
                if ticket:
                    line = self._resolve_line(ticket)
                    if line.get("url"):
                        play_url = line["url"]
                        url_kind = line.get("url_kind", "")

        # 回退候选：官方线路优先，全部失败才轮到普通线路（保证能播）
        official_lines = [ln for ln in lines if self._is_official_line(ln)]
        fallback_lines = official_lines + [ln for ln in lines if ln not in official_lines]

        # 未指定线路或指定线路失败：先试官方线路 resolve-line 二次解析
        if not play_url:
            candidates = [ln for ln in fallback_lines if ln.get("selected")] or fallback_lines
            for ln in candidates:
                ticket = (_txt(ln.get("url") or "")).replace("resolve://", "")
                if not ticket:
                    continue
                line = self._resolve_line(ticket)
                if line.get("url"):
                    play_url = line["url"]
                    url_kind = line.get("url_kind", "")
                    break

        # 最后兜底：免解析的 m3u8 直链线路（普通线路，按返回顺序）
        if not play_url:
            for ln in fallback_lines:
                if ln.get("url_kind") == "m3u8" and not ln.get("resolve_required") and ln.get("url"):
                    play_url = ln["url"]
                    url_kind = "m3u8"
                    break

        return {
            "parse": 0,
            "playUrl": "",
            "url": play_url,
            "header": {"User-Agent": self.ua},
        }

    # ↓↓↓ TVBox 框架 base.spider 抽象方法必须实现，缺失会导致实例化失败 ↓↓↓
    def getName(self):
        return self.name

    def localProxy(self, param):
        return [404, "text/plain", b""]

    def isVideoFormat(self, url):
        return False

    def manualVideoCheck(self):
        return 0

    def destroy(self):
        pass

    # ================= 工具方法 =================

    def _short_line_name(self, label):
        """线路显示名简化：'1080P-官方Z · 普通话' -> '官方Z'；
        含4K的保留4K前缀以区分（'4K海外-官方C' -> '4K官方C'）；其他原样返回"""
        label = _txt(label)
        if "官方" in label:
            base = label.split("·")[0].strip()
            for seg in reversed(base.split("-")):
                if "官方" in seg:
                    name = seg.strip()
                    if "4K" in base.upper() and not name.upper().startswith("4K"):
                        name = "4K" + name
                    return name
        return label

    def _is_official_line(self, ln):
        """官方线路：label含"官方"，或 provider_id 为 official-*/bytevod-*"""
        label = _txt(ln.get("label") or "")
        provider = (_txt(ln.get("provider_id") or "")).lower()
        if "官方" in label:
            return True
        if provider.startswith("official") or provider.startswith("bytevod"):
            return True
        return False

    def _fetch_all_episodes(self, vid, inline_eps):
        episodes = list(inline_eps)
        try:
            offset = len(episodes)
            while True:
                data = self._get(u"/v1/catalog/{}/episodes".format(_txt(vid)),
                                 u"?limit=48&offset={}".format(offset))
                eps = data.get("episodes", []) or []
                if not eps:
                    break
                episodes.extend(eps)
                page_info = data.get("episode_pagination", {}) or {}
                if not page_info.get("has_more"):
                    break
                offset += len(eps)
        except Exception as e:
            _log(u"懂片帝 fetch episodes error: {}".format(e))
        return episodes

    def _parse_card(self, card):
        remarks = _txt(card.get("remarks", "") or "")
        return {
            "vod_id": _txt(card.get("id", "")),
            "vod_name": _txt(card.get("title", "") or card.get("normalized_title", "")),
            "vod_pic": _txt(card.get("poster_url", "") or card.get("backdrop_url", "")),
            "vod_remarks": remarks,
            "vod_year": _txt(card.get("year", "") or ""),
            "vod_area": _txt(card.get("area", "") or ""),
            "vod_director": _tags(card.get("directors", []) or []),
            "vod_actor": _tags(card.get("actors", []) or []),
            "vod_type": _tags(card.get("genres", []) or []),
            "vod_content": _clean_text(card.get("content", "") or card.get("description", "") or card.get("blurb", "")),
        }
