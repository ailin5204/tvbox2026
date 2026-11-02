# -*- coding: utf-8 -*-
# 推特APP T4 检修版（就地修复自原稿 368 行，getName 推特APP）
# 保留原稿核心机制：token 域名每次随机生成 https://<随机5-10位>.<hs>.work，
# hs 池 wcyfhknomg / pdcqllfomw / alxhzjvean / bqeaaxzplt / hfbtpixjso，
# POST /api/user/traveler 拿 token/imgDomain/host；API 走 host + 路径，
# 响应 encData 用 AES-128-CBC（key=iv=b64decode('SmhiR2NpT2lKSVV6STFOaQ==')）解密。
# API 路径：classifyList / queryVideoByClassifyId / queryPersonVideoByType /
# getRankVideos / search/keyWord / can/watch / m3u8/decode/authPath。
# 存活结论（2026-10-31 沙箱）：5 个 hs 后缀 traveler 全部读超时/服务端断连，
# 但域名能解析（不是 DNS 死亡），属沙箱出口被挡、不是已证实站死，盒端国内网才是定论；
# 故本版继续检修，六接口改由夹具 + 真 Jython 回放验证，实站 token 链路待盒端复验。
# 本版全卡大图（用户明确要求）：_BIG = {"type": "rect", "ratio": 1.33} 单层定义，
# 卡片 style=dict(_BIG)，不包 style 键、无嵌套 style。
# 简介清洗：先 strip 标签再单次 unescape，禁止双重解码。
import re
import json
import time
import random
import string
import hashlib

try:
    from base64 import b64decode as _b64decode
except Exception:
    _b64decode = None

# ---- py2/py3 双回退（顶层不留任何 py3 独占硬导入）----
try:
    from urllib.parse import quote as _quote, unquote as _unquote, parse_qs as _parse_qs
except Exception:
    from urllib import quote as _quote, unquote as _unquote
    from urlparse import parse_qs as _parse_qs
try:
    import urllib.request as _urlrequest
    import urllib.error as _urlerror
except Exception:
    import urllib2 as _urlrequest
    import urllib2 as _urlerror
try:
    import requests as _requests
except Exception:
    _requests = None
try:
    from Crypto.Cipher import AES as _CryptoAES
    from Crypto.Util.Padding import unpad as _crypto_unpad
except Exception:
    _CryptoAES = None
    _crypto_unpad = None

try:
    _PY3 = True
    _STR = str
    _text_type = str
    _binary_type = bytes
    unicode  # noqa: F821
    _PY3 = False
except Exception:
    _PY3 = True
    _STR = str
    _text_type = str
    _binary_type = bytes
if not _PY3:
    _STR = basestring  # noqa: F821
    _text_type = unicode  # noqa: F821


def _txt(x, default=u""):
    if x is None:
        return default
    if isinstance(x, _text_type):
        return x
    if isinstance(x, _binary_type):
        try:
            return x.decode("utf-8")
        except Exception:
            return x.decode("utf-8", "ignore")
    try:
        return _text_type(x)
    except Exception:
        return default


def _bytes(x):
    if isinstance(x, _binary_type):
        return x
    if isinstance(x, _text_type):
        return x.encode("utf-8")
    return _bytes(_txt(x))


def _b2i(b):
    # py2 下 bytes 下标出单字符 str，py3 出 int；统一转 int
    if isinstance(b, int):
        return b
    return ord(b)


def _quote_txt(s):
    # py2 urllib.quote 不接受 unicode（含中文必 KeyError），先转 utf-8 字节再 quote；
    # py3 直接 quote 字符串。原稿只在 py3 下跑，CPython 测不出此坑。
    if _PY3:
        return _quote(_txt(s))
    return _quote(_bytes(_txt(s)))


def _unquote_txt(s):
    if _PY3:
        return _txt(_unquote(_txt(s)))
    return _txt(_unquote(_bytes(_txt(s))))


def _unescape_once(s):
    s = _txt(s)
    s = re.sub(r"<[^>]+>", "", s)
    s = s.replace("&lt;", "<").replace("&gt;", ">").replace("&quot;", '"')
    s = s.replace("&#39;", "'").replace("&#039;", "'").replace("&amp;", "&")
    return s.strip()


# ---- 纯 Python AES 解密（Crypto 不可用时回退；只用于解密 encData）----
def _gf_mul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1B
        b >>= 1
    return p


def _gf_inv(a):
    if a == 0:
        return 0
    r = 1
    for _ in range(254):
        r = _gf_mul(r, a)
    return r


def _rotl8(x, n):
    return ((x << n) | (x >> (8 - n))) & 0xFF


_SBOX = []
for _i in range(256):
    _inv = _gf_inv(_i)
    _SBOX.append(_inv ^ _rotl8(_inv, 1) ^ _rotl8(_inv, 2) ^ _rotl8(_inv, 3) ^ _rotl8(_inv, 4) ^ 0x63)
_INV_SBOX = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV_SBOX[_v] = _i
_RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]


def _aes_expand_key(key_bytes):
    key = [_b2i(b) for b in bytearray(key_bytes)]
    nk = len(key) // 4
    nr = nk + 6
    w = [key[i * 4:(i + 1) * 4] for i in range(nk)]
    for i in range(nk, 4 * (nr + 1)):
        temp = list(w[i - 1])
        if i % nk == 0:
            temp = [_SBOX[temp[1]] ^ _RCON[i // nk - 1], _SBOX[temp[2]], _SBOX[temp[3]], _SBOX[temp[0]]]
        elif nk > 6 and i % nk == 4:
            temp = [_SBOX[t] for t in temp]
        w.append([w[i - nk][j] ^ temp[j] for j in range(4)])
    return w, nr


def _aes_decrypt_block(block_bytes, round_keys, nr):
    st = [_b2i(b) for b in bytearray(block_bytes)]

    def _add_rk(s, rnd):
        for c in range(4):
            for r in range(4):
                s[r + 4 * c] ^= round_keys[rnd * 4 + c][r]

    def _inv_shift_rows(s):
        out = list(s)
        for r in range(1, 4):
            for c in range(4):
                out[r + 4 * c] = s[r + 4 * ((c - r) % 4)]
        return out

    def _inv_sub(s):
        return [_INV_SBOX[v] for v in s]

    def _inv_mix(s):
        out = [0] * 16
        for c in range(4):
            col = s[4 * c:4 * c + 4]
            out[4 * c + 0] = _gf_mul(col[0], 14) ^ _gf_mul(col[1], 11) ^ _gf_mul(col[2], 13) ^ _gf_mul(col[3], 9)
            out[4 * c + 1] = _gf_mul(col[0], 9) ^ _gf_mul(col[1], 14) ^ _gf_mul(col[2], 11) ^ _gf_mul(col[3], 13)
            out[4 * c + 2] = _gf_mul(col[0], 13) ^ _gf_mul(col[1], 9) ^ _gf_mul(col[2], 14) ^ _gf_mul(col[3], 11)
            out[4 * c + 3] = _gf_mul(col[0], 11) ^ _gf_mul(col[1], 13) ^ _gf_mul(col[2], 9) ^ _gf_mul(col[3], 14)
        return out

    _add_rk(st, nr)
    for rnd in range(nr - 1, 0, -1):
        st = _inv_shift_rows(st)
        st = _inv_sub(st)
        _add_rk(st, rnd)
        st = _inv_mix(st)
    st = _inv_shift_rows(st)
    st = _inv_sub(st)
    _add_rk(st, 0)
    return bytes(bytearray(st))


def _aes_cbc_decrypt_pure(data, key):
    if len(data) == 0 or len(data) % 16 != 0:
        return b""
    round_keys, nr = _aes_expand_key(key)
    iv = list(bytearray(key))
    out = bytearray()
    prev = iv
    for off in range(0, len(data), 16):
        blk = _aes_decrypt_block(data[off:off + 16], round_keys, nr)
        for i in range(16):
            out.append(_b2i(blk[i]) ^ prev[i])
        prev = [_b2i(b) for b in bytearray(data[off:off + 16])]
    if out:
        pad = out[-1]
        if 0 < pad <= 16 and all(v == pad for v in out[-pad:]):
            out = out[:-pad]
    return bytes(out)


# ---- HTTP 响应包装（requests / urllib 两路统一）----
class _Resp(object):
    def __init__(self, status=200, content=b"", headers=None, url=""):
        self.status_code = status
        self.code = status
        self.content = content if isinstance(content, _binary_type) else _bytes(content)
        self.headers = headers or {}
        self.url = url

    @property
    def text(self):
        try:
            return self.content.decode("utf-8")
        except Exception:
            return self.content.decode("utf-8", "ignore")

    def json(self):
        return json.loads(self.text)

    def raise_for_status(self):
        if self.status_code >= 400:
            raise Exception("http %s" % self.status_code)


def _http_urllib(method, url, data_bytes=None, headers=None, timeout=12):
    headers = headers or {}
    req = _urlrequest.Request(_txt(url), data=data_bytes, headers=dict(headers))
    if not _PY3:
        # py2 urllib2 的 Request 不接受 method 参数，GET 靠无 data、POST 靠有 data 判定
        pass
    else:
        try:
            req.get_method = lambda: method
        except Exception:
            pass
    try:
        import ssl as _ssl
        ctx = _ssl._create_unverified_context()
        resp = _urlrequest.urlopen(req, timeout=timeout, context=ctx)
    except TypeError:
        resp = _urlrequest.urlopen(req, timeout=timeout)
    raw = resp.read()
    hdrs = {}
    try:
        for k, v in resp.info().items():
            hdrs[k] = v
    except Exception:
        pass
    try:
        code = resp.getcode()
    except Exception:
        code = 200
    try:
        import gzip as _gzip
        import io as _io
        enc = ""
        for k, v in hdrs.items():
            if k.lower() == "content-encoding":
                enc = v
        if raw[:2] == b"\x1f\x8b" or enc == "gzip":
            raw = _gzip.GzipFile(fileobj=_io.BytesIO(raw)).read()
    except Exception:
        pass
    return _Resp(code, raw, hdrs, url)


# ---- BaseSpider 四级兜底 ----
try:
    from base.spider import Spider as BaseSpider
except Exception:
    try:
        from base.spider import Spider as BaseSpider  # noqa: F811
    except Exception:
        class BaseSpider(object):
            _mem_cache = {}

            def getName(self):
                return ""

            def init(self, extend=""):
                pass

            def fetch(self, url, headers=None, timeout=12, **kw):
                return _http_urllib("GET", url, None, headers, timeout)

            def post(self, url, data=None, json=None, headers=None, timeout=12, **kw):
                body = None
                hdrs = dict(headers or {})
                if json is not None:
                    body = _bytes(json.dumps(json))
                    hdrs.setdefault("Content-Type", "application/json")
                elif data is not None:
                    body = data if isinstance(data, _binary_type) else _bytes(data)
                return _http_urllib("POST", url, body, hdrs, timeout)

            def getCache(self, key):
                return self._mem_cache.get(key)

            def setCache(self, key, value):
                self._mem_cache[key] = value
                return "ok"

            def delCache(self, key):
                self._mem_cache.pop(key, None)
                return "ok"

            def getProxyUrl(self):
                return ""

            def log(self, *a):
                pass


_BIG = {"type": "rect", "ratio": 1.33}
_AES_KEY_B64 = "SmhiR2NpT2lKSVV6STFOaQ=="


class Spider(BaseSpider):

    PIC_RE = re.compile(r"(?:(?:jpe|image|img|cover|video|pic)/[^\s\"'&,;]+|[\w/\-.]+\.(?:jpg|jpeg|png|gif|webp|bmp))", re.I)

    def getName(self):
        return u"推特APP"

    def init(self, extend=""):
        self.hs = ["wcyfhknomg", "pdcqllfomw", "alxhzjvean", "bqeaaxzplt", "hfbtpixjso"]
        self.ua = "Mozilla/5.0 (Linux; Android 11; M2012K10C Build/RP1A.200720.011; wv) AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/87.0.4280.141 Mobile Safari/537.36;SuiRui/twitter/ver=1.4.4"
        self.did = self.getdid()
        # token 懒获取：init 不阻塞首页，第一次调接口时 _ensure_token() 再拿；
        # 拿不到时各接口返回空列表/空对象，不崩。
        self.token = ""
        self.phost = ""
        self.host = ""
        self.api_cache = {}
        self.img_cache = {}
        self._token_retry_after = 0

    def _ensure_state(self):
        if not hasattr(self, "hs") or not getattr(self, "hs", None):
            self.init("")
        if not hasattr(self, "api_cache"):
            self.api_cache = {}
        if not hasattr(self, "img_cache"):
            self.img_cache = {}

    def isVideoFormat(self, url):
        return False

    def manualVideoCheck(self):
        return 0

    def action(self, action):
        pass

    def destroy(self):
        pass

    def homeContent(self, filter):
        self._ensure_state()
        self._ensure_token()
        data = self._api("/api/video/classifyList") if self.host else {}
        classes = [{"type_name": u"精选", "type_id": "jx"}]
        for k in data.get("data", []) or []:
            tid = _txt(k.get("classifyId", ""))
            name = _txt(k.get("classifyTitle", ""))
            if tid and name:
                classes.append({"type_name": name, "type_id": tid})
        sort = [{"key": "fl", "name": u"分类", "value": [{"n": u"最近更新", "v": "1"}, {"n": u"最多播放", "v": "2"}, {"n": u"好评榜", "v": "3"}]}]
        filters = {}
        for c in classes:
            if c["type_id"] != "jx":
                filters[c["type_id"]] = sort
        filters["jx"] = [{"key": "type", "name": u"精选", "value": [{"n": u"日榜", "v": "1"}, {"n": u"周榜", "v": "2"}, {"n": u"月榜", "v": "3"}, {"n": u"总榜", "v": "4"}]}]
        lst = []
        try:
            lst = self.homeVideoContent().get("list", []) or []
        except Exception:
            lst = []
        return {"class": classes, "filters": filters, "list": lst}

    def homeVideoContent(self):
        self._ensure_state()
        try:
            return {"list": self.categoryContent("jx", "1", False, {"type": "1"}).get("list", [])}
        except Exception:
            return {"list": []}

    def categoryContent(self, tid, pg, filter, extend):
        self._ensure_state()
        self._ensure_token()
        try:
            page = int(pg or 1)
        except Exception:
            page = 1
        if page < 1:
            page = 1
        ext = self._ext(extend)
        tid_s = _txt(tid)
        path = "/api/video/queryVideoByClassifyId?pageSize=20&page=%s&classifyId=%s&sortType=%s" % (page, tid_s, ext.get("fl", "1"))
        clicked = "click" in tid_s
        if clicked:
            path = "/api/video/queryPersonVideoByType?pageSize=20&page=%s&userId=%s" % (page, tid_s.replace("click", ""))
        if tid_s == "jx":
            path = "/api/video/getRankVideos?pageSize=20&page=%s&type=%s" % (page, ext.get("type", "1"))
        data = self._api(path) if self.host else {}
        arr = data.get("data", []) if isinstance(data.get("data", []), list) else data.get("videoList", [])
        lst = self.items(arr or [], clicked)
        per = len(lst)
        if per >= 20:
            pagecount = page + 1
            total = page * 20
        else:
            pagecount = page
            total = (page - 1) * 20 + per
        return {"list": lst, "page": page, "pagecount": pagecount, "limit": per if per else 20, "total": total}

    def detailContent(self, array):
        self._ensure_state()
        raw = _txt(array[0]) if array else u""
        if "?" not in raw and "%3f" in raw.lower():
            raw = _unquote_txt(raw)
        click = raw.endswith("click")
        if click:
            raw = raw[:-5]
        pp = raw.split("?", 3)
        vid = pp[0] if len(pp) > 0 else raw
        uid = pp[1] if len(pp) > 1 else ""
        nick = _unquote_txt(pp[2]) if len(pp) > 2 else u"推特APP"
        title = _unquote_txt(pp[3]) if len(pp) > 3 else ""
        name = (title or nick or u"推特APP").replace("$", u"＄")
        clj = nick
        if not click and uid:
            clj = "[a=cr:" + json.dumps({"id": uid + "click", "name": nick}) + "/]" + nick + "[/a]"
        # 站内详情不调接口、无独立简介字段，vod_content 取标题本身并单次清洗，不编造简介
        vod = {"vod_id": raw, "vod_name": name, "vod_pic": "", "vod_actor": "",
               "vod_director": clj, "vod_content": _unescape_once(name),
               "vod_play_from": u"酷鱼专线", "vod_play_url": name + "$" + vid}
        return {"list": [vod]}

    def searchContent(self, key, quick, pg="1"):
        self._ensure_state()
        self._ensure_token()
        try:
            page = int(pg or 1)
        except Exception:
            page = 1
        if page < 1:
            page = 1
        data = self._api("/api/search/keyWord?pageSize=20&page=%s&searchWord=%s&searchType=1" % (page, _quote_txt(key))) if self.host else {}
        lst = self.items(data.get("videoList", []) or [], False)
        per = len(lst)
        if per >= 20:
            pagecount = page + 1
            total = page * 20
        else:
            pagecount = page
            total = (page - 1) * 20 + per
        return {"list": lst, "page": page, "pagecount": pagecount, "limit": per if per else 20, "total": total}

    def searchContentPage(self, key, quick, pg):
        return self.searchContent(key, quick, str(pg or "1"))

    def playerContent(self, flag, id, vipFlags=None):
        self._ensure_state()
        self._ensure_token()
        vid = _txt(id)
        data = self.watch(vid) if self.host else {}
        ak = data.get("authKey", "")
        vu = data.get("videoUrl", "")
        url = ""
        if ak and vu:
            url = "%s/api/m3u8/decode/authPath?auth_key=%s&path=%s" % (self.host, ak, vu)
        if not url:
            url = data.get("playPath", "") or ""
        if url:
            return {"parse": 0, "playUrl": "", "url": url, "header": self.headers()}
        # 无直链不冒充 parse=0，交壳子嗅探（本站无播放页可嗅探，实为无流信号）
        return {"parse": 1, "playUrl": "", "url": "", "header": self.headers()}

    def localProxy(self, param):
        self._ensure_state()
        tp, u = self.proxy_param(param)
        if not u:
            return [404, "text/plain", b""]
        ct, body = self.img_asset(u)
        if not isinstance(body, _binary_type):
            body = _bytes(body)
        return [200, ct or "image/jpeg", body]

    def items(self, arr, clicked=False):
        res = []
        for k in arr or []:
            cover = k.get("coverImg") or []
            if isinstance(cover, list) and cover:
                pic = cover[0]
            elif isinstance(cover, _STR):
                pic = cover
            else:
                pic = ""
            vid = _txt(k.get("videoId", ""))
            uid = _txt(k.get("userId", ""))
            nick = _txt(k.get("nickName", ""))
            if not vid:
                continue
            vid_id = u"%s?%s?%s?%s" % (vid, uid, _quote_txt(nick), _quote_txt(_txt(k.get("title") or nick or vid)))
            if clicked:
                vid_id = vid_id + "click"
            res.append({"vod_id": vid_id, "vod_name": _txt(k.get("title") or nick or vid),
                        "vod_pic": self.proxypic(pic), "vod_remarks": self.dtim(k.get("playTime")),
                        "style": dict(_BIG)})
        return res

    def _ext(self, extend):
        if isinstance(extend, _STR):
            try:
                return json.loads(extend)
            except Exception:
                return {}
        return extend if isinstance(extend, dict) else {}

    def _api(self, path, post=None):
        self._ensure_state()
        if not self.host:
            return {}
        url = self.host + path if path.startswith("/") else path
        try:
            key = ("POST:" if post is not None else "GET:") + url
            if key in self.api_cache:
                return self.api_cache[key]
            r = self.req(url, post)
            if r is None:
                return {}
            j = r.json()
            data = self.aes(j.get("encData", "")) if j.get("encData") else j
            if len(self.api_cache) > 80:
                self.api_cache.clear()
            self.api_cache[key] = data
            return data
        except Exception:
            return {}

    def watch(self, vid):
        self._ensure_state()
        if not self.host:
            return {}
        try:
            url = self.host + "/api/video/can/watch?videoId=%s" % vid
            r = self.req(url, None)
            if r is None:
                return {}
            j = r.json()
            return self.aes(j.get("encData", "")) if j.get("encData") else j
        except Exception:
            return {}

    def _shell_req(self, method, url, post=None):
        # 壳子 BaseSpider 自带的 fetch/post（若存在）优先于 requests/urllib
        try:
            fn = None
            if post is not None:
                fn = getattr(self, "post", None)
            else:
                fn = getattr(self, "fetch", None)
            if not callable(fn):
                return None
            # 区分回退基类（其 fetch/post 已是 urllib 实现，可直接用）与壳子实现：
            # 两者都返回 _Resp 或类 requests 响应，下方统一包装。
            if post is not None:
                r = fn(url, json=post, headers=self.headers(), timeout=12)
            else:
                r = fn(url, headers=self.headers(), timeout=12)
            if r is None:
                return None
            if isinstance(r, _Resp):
                return r
            content = b""
            if hasattr(r, "content") and r.content is not None:
                content = r.content if isinstance(r.content, _binary_type) else _bytes(r.content)
            elif hasattr(r, "text") and r.text:
                content = _bytes(r.text)
            hdrs = {}
            try:
                for k, v in r.headers.items():
                    hdrs[k] = v
            except Exception:
                pass
            code = getattr(r, "status_code", getattr(r, "code", 200)) or 200
            return _Resp(code, content, hdrs, url)
        except Exception:
            return None

    def req(self, url, post=None):
        r = self._shell_req("POST" if post is not None else "GET", url, post)
        if r is not None:
            return r
        headers = self.headers()
        if _requests is not None:
            try:
                if post is not None:
                    rr = _requests.post(url, json=post, headers=headers, timeout=12, verify=False)
                else:
                    rr = _requests.get(url, headers=headers, timeout=12, verify=False)
                return _Resp(rr.status_code, rr.content, dict(rr.headers), url)
            except Exception:
                pass
        try:
            body = None
            hdrs = dict(headers)
            if post is not None:
                body = _bytes(json.dumps(post))
                hdrs.setdefault("Content-Type", "application/json")
            return _http_urllib("POST" if post is not None else "GET", url, body, hdrs, 12)
        except Exception:
            return None

    def _post_json(self, url, data, headers):
        if _requests is not None:
            try:
                rr = _requests.post(url, json=data, headers=headers, timeout=6, verify=False)
                return _Resp(rr.status_code, rr.content, dict(rr.headers), url)
            except Exception:
                pass
        try:
            hdrs = dict(headers)
            hdrs.setdefault("Content-Type", "application/json")
            return _http_urllib("POST", url, _bytes(json.dumps(data)), hdrs, 6)
        except Exception:
            return None

    def _ensure_token(self):
        self._ensure_state()
        if self.token and self.host:
            return True
        now = int(time.time())
        if self._token_retry_after and now < self._token_retry_after:
            return False
        token, phost, host = self.gettoken()
        if token and host:
            self.token, self.phost, self.host = token, phost, host
            return True
        self._token_retry_after = now + 60
        return False

    def gettoken(self):
        # 先试缓存域名，再按 hs 顺序各试一个随机子域名；全部失败返回空三元组，不抛异常
        try:
            line = self.getCache("twline") or ""
        except Exception:
            line = ""
        if line:
            try:
                d = _txt(line).split("|", 1)[0]
                r = self.tryline(d)
                if r[0]:
                    return r
            except Exception:
                pass
        for suf in self.hs:
            k = random.randint(5, 10)
            rand = "".join(random.choice(string.ascii_lowercase + string.digits) for _ in range(k))
            domain = "https://%s.%s.work" % (rand, suf)
            try:
                r = self.tryline(domain)
                if r[0]:
                    try:
                        self.setCache("twline", domain + "|" + self.did)
                    except Exception:
                        pass
                    return r
            except Exception:
                continue
        return "", "", ""

    def tryline(self, domain):
        try:
            sign, t = self.getsign()
            headers = {"User-Agent": self.ua, "Accept": "application/json", "deviceid": self.did, "t": t, "s": sign}
            data = {"deviceId": self.did, "tt": "U", "code": "##X-4m6Goo4zzPi1hF##", "chCode": "tt09"}
            r = self._post_json(domain + "/api/user/traveler", data, headers)
            if r is None:
                return "", "", ""
            r.raise_for_status()
            data1 = r.json()["data"]
            if data1.get("token") and data1.get("imgDomain"):
                return data1["token"], data1["imgDomain"], domain
        except Exception:
            pass
        return "", "", ""

    def headers(self):
        sign, t = self.getsign()
        return {"User-Agent": self.ua, "deviceid": self.did, "t": t, "s": sign, "aut": self.token}

    def getsign(self):
        t = str(int(time.time() * 1000))
        return self.md5(t), t

    def aes(self, word):
        if not word:
            return {}
        try:
            if _b64decode is None:
                return {}
            key = _b64decode(_AES_KEY_B64)
            raw = _b64decode(word)
            if _CryptoAES is not None and _crypto_unpad is not None:
                cipher = _CryptoAES.new(key, _CryptoAES.MODE_CBC, key)
                decrypted = _crypto_unpad(cipher.decrypt(raw), _CryptoAES.block_size)
                return json.loads(decrypted.decode("utf-8"))
            plain = _aes_cbc_decrypt_pure(raw, key)
            return json.loads(plain.decode("utf-8"))
        except Exception:
            return {}

    def dtim(self, seconds):
        try:
            seconds = int(seconds or 0)
            hours = seconds // 3600
            remaining = seconds % 3600
            minutes = remaining % 3600 // 60
            remaining = remaining % 60
            if hours > 0:
                return "%02d:%02d:%02d" % (hours, minutes, remaining)
            return "%02d:%02d" % (minutes, remaining)
        except Exception:
            return ""

    def getdid(self):
        did = ""
        try:
            did = self.getCache("did") or ""
        except Exception:
            did = ""
        if not did:
            did = self.md5(str(int(time.time())) + str(random.randint(1000, 9999)))
            try:
                self.setCache("did", did)
            except Exception:
                pass
        return did

    def md5(self, text):
        return hashlib.md5(_bytes(text)).hexdigest()

    def proxypic(self, u):
        if not u:
            return ""
        p = ""
        try:
            p = self.getProxyUrl() or ""
        except Exception:
            p = ""
        if "do=py" not in p:
            p = "http://127.0.0.1:9978/proxy?do=py"
        elif "/proxy" not in p:
            p = p.replace("?do=py", "/proxy?do=py")
        sep = "&" if "?" in p else "?"
        name = u"推特APP"
        try:
            name = self.getName() or u"推特APP"
        except Exception:
            pass
        return p + sep + "type=" + name + "&key=" + name + "&u=" + u + "&url=" + u

    def proxy_param(self, param):
        tp, u = self._param_strict(param)
        if u:
            return tp, u
        vals = []
        try:
            if isinstance(param, dict):
                for k, v in list(param.items()):
                    vals.append(_txt(v))
                    vals.append(_txt(k))
            elif param is not None:
                vals.append(_txt(param))
        except Exception:
            return "img", ""
        for v in vals:
            try:
                m = self.PIC_RE.search(_unquote_txt(v))
                if m:
                    return "img", m.group(0)
            except Exception:
                continue
        return "img", ""

    def _param_strict(self, param):
        try:
            if isinstance(param, dict):
                u = param.get("u") or param.get("url") or param.get("img") or param.get("src") or ""
                if u:
                    return param.get("do") or param.get("type") or "img", _unquote_txt(u)
                q = _parse_qs(_txt(param.get("query", "") or param.get("params", "") or param.get("param", "") or ""))
            else:
                q = _parse_qs(_txt(param))
            return (q.get("do") or q.get("type") or ["img"])[0], _unquote_txt((q.get("u") or q.get("url") or q.get("img") or q.get("src") or [""])[0])
        except Exception:
            return "img", ""

    def imgurl(self, u):
        if not u:
            return ""
        if _txt(u).startswith("http"):
            return u
        return (self.phost or "") + u

    def img_asset(self, u):
        if u in self.img_cache:
            return self.img_cache[u]
        try:
            r = self.reqimg(self.imgurl(u))
            if r is None:
                return "text/plain", b""
            body = self.img(r.content, 100, "2020-zq3-888")
            ct = ""
            try:
                ct = r.headers.get("Content-Type", "image/jpeg")
            except Exception:
                ct = "image/jpeg"
            if len(self.img_cache) > 160:
                self.img_cache.clear()
            self.img_cache[u] = (ct, body)
            return ct, body
        except Exception:
            return "text/plain", b""

    def reqimg(self, url):
        try:
            r = self.fetch(url, headers={"User-Agent": self.ua}, timeout=12)
            if r is not None:
                return r
        except Exception:
            pass
        if _requests is not None:
            try:
                rr = _requests.get(url, headers={"User-Agent": self.ua}, timeout=15, verify=False)
                return _Resp(rr.status_code, rr.content, dict(rr.headers), url)
            except Exception:
                pass
        try:
            return _http_urllib("GET", url, None, {"User-Agent": self.ua}, 12)
        except Exception:
            return None

    def img(self, data, length, key):
        GIF = b"\x47\x49\x46"
        JPG = b"\xff\xd8\xff"
        PNG = b"\x89\x50\x4e\x47\x0d\x0a\x1a\x0a"
        if len(data) > 7 and (data[:3] == GIF or data[:3] == JPG or data[1:8] == PNG[1:8]):
            return data
        key_bytes = key.encode("utf-8")
        result = bytearray(data)
        for i in range(min(length, len(result))):
            result[i] ^= key_bytes[i % len(key_bytes)]
        return bytes(result)
