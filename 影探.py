# -*- coding: utf-8 -*-
# 影探4K：由 影探4k.js 移植到鱼壳 webhtv 站点注入使用的 Python Spider。
# 用法：把本文件放到手机 /sdcard/py/影探4K.py，站点配置 api 填 file:///sdcard/py/影探4K.py
import base64
import json
import re
import time
import urllib.parse

import requests

# [修复] 顶层 import Crypto 无保护会导致缺库时 App 直接崩溃
# 改为软导入：缺库时抛清晰异常，只在调用加解密时失败，不影响 App 启动
try:
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import unpad
except Exception:
    _HAS_CRYPTO = True
    _SBOX = [
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]
    _INV_SBOX = [0] * 256
    for _i, _v in enumerate(_SBOX):
        _INV_SBOX[_v] = _i
    _RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36]

    def _xtime(a):
        return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff

    def _mul(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a = _xtime(a)
            b >>= 1
        return r & 0xff

    def _expand_key(key):
        w = [list(key[i * 4:i * 4 + 4]) for i in range(4)]
        for i in range(4, 44):
            t = list(w[i - 1])
            if i % 4 == 0:
                t = t[1:] + t[:1]
                t = [_SBOX[x] for x in t]
                t[0] ^= _RCON[i // 4 - 1]
            w.append([w[i - 4][j] ^ t[j] for j in range(4)])
        return w

    def _decrypt_block(block, w):
        s = [[block[c * 4 + r] for r in range(4)] for c in range(4)]
        for c in range(4):
            for r in range(4):
                s[c][r] ^= w[40 + c][r]
        for rnd in range(9, 0, -1):
            for r in range(1, 4):
                row = [s[c][r] for c in range(4)]
                for c in range(4):
                    s[c][r] = row[(c - r) % 4]
            for c in range(4):
                for r in range(4):
                    s[c][r] = _INV_SBOX[s[c][r]]
            for c in range(4):
                for r in range(4):
                    s[c][r] ^= w[rnd * 4 + c][r]
            for c in range(4):
                a = [s[c][r] for r in range(4)]
                s[c][0] = _mul(a[0],14) ^ _mul(a[1],11) ^ _mul(a[2],13) ^ _mul(a[3],9)
                s[c][1] = _mul(a[0],9) ^ _mul(a[1],14) ^ _mul(a[2],11) ^ _mul(a[3],13)
                s[c][2] = _mul(a[0],13) ^ _mul(a[1],9) ^ _mul(a[2],14) ^ _mul(a[3],11)
                s[c][3] = _mul(a[0],11) ^ _mul(a[1],13) ^ _mul(a[2],9) ^ _mul(a[3],14)
        for r in range(1, 4):
            row = [s[c][r] for c in range(4)]
            for c in range(4):
                s[c][r] = row[(c - r) % 4]
        for c in range(4):
            for r in range(4):
                s[c][r] = _INV_SBOX[s[c][r]]
        for c in range(4):
            for r in range(4):
                s[c][r] ^= w[c][r]
        return bytes(s[c][r] for c in range(4) for r in range(4))

    class _PureAES(object):
        block_size = 16
        MODE_CBC = 2
        def __init__(self, key, mode, iv):
            self._w = _expand_key(bytes(key)[:16])
            self._iv = bytes(iv)[:16]
        def decrypt(self, data):
            out = b''
            prev = self._iv
            for i in range(0, len(data), 16):
                blk = bytes(data[i:i + 16])
                out += bytes(a ^ b for a, b in zip(_decrypt_block(blk, self._w), prev))
                prev = blk
            return out

    class _AESShim(object):
        block_size = 16
        MODE_CBC = 2
        @staticmethod
        def new(key, mode, iv):
            return _PureAES(key, mode, iv)

    AES = _AESShim

    def unpad(data, *a, **k):
        if data and 0 < data[-1] <= 16:
            return data[:-data[-1]]
        return data

try:
    from base.spider import Spider
except ImportError:
    import sys
    sys.path.append('..')
    from base.spider import Spider

KEY = 'yingtan4k'
HOST = 'http://cms.lyyytv.cn'
CMS_KEY = 'wP5bvxoc3yv7FoBQENFZuAF0EUYr4LTy'

# 解析接口（对齐 yt4k.js：fys.lyyytv.cn / parsesId=3）
PARSE_IDS = (5, 6, 4, 2, 1)
PARSE_TPL = 'http://fys.lyyytv.cn/api/index?parsesId=%d&appid=10001&videoUrl='
HEADERS = {'User-Agent': 'okhttp/4.12.0'}
# 解析请求/回源头：对齐 JS 的 PH，避免 gzip 花屏
PARSE_HEADERS = {'User-Agent': 'okhttp/4.12.0', 'Accept-Encoding': 'identity'}

# baidu.con 前缀加密常量（对齐 yt4k.js）
DEC_PREFIX = 'https://baidu.con/'
# 解析重试轮数与退避基数（秒）
PARSE_ROUNDS = 3
PARSE_BACKOFF = 0.35
# 同一原始地址解析结果缓存窗口（秒）
PLAY_CACHE_TTL = 120

PAGE_LIMIT = 20
FILTER_NAMES = {
    'class': '类型', 'area': '地区', 'lang': '语言', 'year': '年份',
    'letter': '字母', 'by': '排序', 'sort': '顺序',
}
HOME_CACHE_TTL = 6 * 3600

_BASE64_RE = re.compile(r'(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?')
_LDMAX_RE = re.compile(r'^https?://ldmax\.cooom/', re.I)
_MEDIA_RE = re.compile(r'\.(?:mp4|m3u8?|flv|avi|mkv|ts|mov|wmv|webm|m4v|mpd)$', re.I)

_home_cache = {}
_play_cache = {}


def text(value):
    return '' if value is None else str(value).strip()


def page_of(value):
    m = re.match(r'\s*[+-]?\d+', '' if value is None else str(value))
    n = int(m.group(0)) if m else 0
    return max(1, n) if n else 1


def list_of(value):
    return value if isinstance(value, list) else []


def object_of(value):
    if isinstance(value, dict):
        return value
    if isinstance(value, str):
        try:
            parsed = json.loads(value)
        except Exception:
            return {}
        return parsed if isinstance(parsed, dict) else {}
    return {}


def get_json(url, headers=None, timeout=15):
    headers = HEADERS if headers is None else headers
    rsp = requests.get(url, headers=headers, timeout=timeout, allow_redirects=True)
    try:
        data = object_of(rsp.json())
    except Exception:
        data = {}
    if not data:
        raise Exception('影探4K：接口未返回有效 JSON')
    return data


def cms(path, params=None):
    params = params or {}
    query = urllib.parse.urlencode(params)
    data = get_json('%s/api.php/app/%s?%s' % (HOST, path, query))
    code = data.get('code')
    if code is not None:
        try:
            ok = int(code) in (1, 200)
        except (TypeError, ValueError):
            ok = False
        if not ok:
            raise Exception('影探4K：CMS 请求失败')
    return data


def decode_base64(value):
    clean = re.sub(r'\s+', '', text(value))
    if not clean or not _BASE64_RE.fullmatch(clean):
        return None
    try:
        return base64.b64decode(clean)
    except Exception:
        return None


def decrypt_lvdou(value):
    """对齐 JS decUrlOne：lvdou+ → 前16 key/后16 iv AES/CBC/PKCS7"""
    original = text(value)
    if not original.startswith('lvdou+'):
        return original
    if not CMS_KEY:
        return original
    try:
        encrypted = decode_base64(original[6:])
        if not encrypted:
            return original
        key = CMS_KEY[:16].encode('utf-8')
        iv = CMS_KEY[16:32].encode('utf-8') if len(CMS_KEY) >= 32 else key
        cipher = AES.new(key, AES.MODE_CBC, iv)
        plain = unpad(cipher.decrypt(encrypted), AES.block_size)
        result = plain.decode('utf-8', errors='replace').strip()
        if result.startswith('http'):
            return result
    except Exception:
        pass
    return original


def is_http_url(value):
    try:
        parsed = urllib.parse.urlparse(text(value))
        return parsed.scheme in ('http', 'https') and bool(parsed.netloc)
    except Exception:
        return False


def is_site_url(value):
    if not is_http_url(value):
        return False
    host = (urllib.parse.urlparse(text(value)).hostname or '').lower()
    return host == 'lyyytv.cn' or host.endswith('.lyyytv.cn')


def is_ldmax_url(value):
    return bool(_LDMAX_RE.match(text(value)))


def decrypt_ldmax(value, depth=0):
    """兼容老加密：ldmax.cooom 前缀"""
    if depth > 5:
        return ''
    url = text(value)
    decoded = decode_base64(url)
    if decoded:
        url = re.sub(r'\s+', '', decoded.decode('utf-8', errors='replace'))
    if not is_ldmax_url(url):
        return url
    path = _LDMAX_RE.sub('', url)
    if len(path) <= 16:
        return ''
    try:
        key = path[:16][::-1].encode('utf-8')
        encrypted = decode_base64(path[16:])
        if not encrypted or len(encrypted) % 16:
            return ''
        cipher = AES.new(key, AES.MODE_CBC, key)
        plain = bytearray(cipher.decrypt(encrypted))
        pad = plain[-1]
        if 0 < pad <= 16:
            del plain[-pad:]
        result = bytes(plain).decode('utf-8', errors='replace').strip()
        return decrypt_ldmax(result, depth + 1) if is_ldmax_url(result) else result
    except Exception:
        return ''


def find_url(value):
    """对齐 JS findUrl：从解析响应 JSON 中挑出 url/playUrl/link/data.url"""
    if not isinstance(value, dict):
        return ''
    for key in ('url', 'playUrl', 'link'):
        v = value.get(key)
        if v:
            return text(v)
    return find_url(value.get('data'))


def resolve_parse(body):
    """
    对齐 JS resolveParse：
      1) JSON 包裹 → 取出 url
      2) https://baidu.con/ 前缀 → 前16位 key=iv，余下 base64 密文 AES/CBC/PKCS7
      3) 明文 URL
    """
    body = text(body)
    if not body:
        return ''

    candidate = body
    if body.startswith('{'):
        try:
            parsed = json.loads(body)
            found = find_url(parsed)
            if found:
                candidate = found
        except Exception:
            pass

    if candidate.startswith(DEC_PREFIX):
        rest = candidate[len(DEC_PREFIX):]
        if len(rest) <= 16:
            return ''
        key = rest[:16].encode('utf-8')
        cipher_b64 = rest[16:]
        # 优先按 base64 密文解密
        try:
            encrypted = base64.b64decode(cipher_b64, validate=False)
            cipher = AES.new(key, AES.MODE_CBC, key)
            plain = unpad(cipher.decrypt(encrypted), AES.block_size)
            result = plain.decode('utf-8', errors='replace').strip()
            if result.startswith('http'):
                return result
        except Exception:
            pass
        # 兜底：密文本身是 raw bytes
        try:
            raw = cipher_b64.encode('latin-1', errors='ignore')
            if raw and len(raw) % 16 == 0:
                cipher = AES.new(key, AES.MODE_CBC, key)
                plain = unpad(cipher.decrypt(raw), AES.block_size)
                result = plain.decode('utf-8', errors='replace').strip()
                if result.startswith('http'):
                    return result
        except Exception:
            pass
        return ''

    return candidate


def parse_url(raw):
    """多 parsesId 轮询解析，任意一个成功即返回。"""
    if not raw:
        return ''
    quoted = urllib.parse.quote(raw, safe="!'()*")
    for pid in PARSE_IDS:
        target = (PARSE_TPL % pid) + quoted
        for rnd in range(PARSE_ROUNDS):
            if rnd > 0:
                time.sleep(rnd * PARSE_BACKOFF)
            try:
                rsp = requests.get(target, headers=PARSE_HEADERS, timeout=30)
                if rsp.status_code == 200 and rsp.text:
                    resolved = resolve_parse(rsp.text)
                    if resolved and resolved.startswith('http'):
                        return resolved
                elif rsp.status_code == 500:
                    break  # 该 parsesId 服务端报错，换下一个
            except Exception:
                pass
    return ''


def is_media_url(url):
    if not is_http_url(url):
        return False
    return bool(_MEDIA_RE.search(urllib.parse.urlparse(text(url)).path))


def home(extend=''):
    cache_key = '%s_home_%s' % (KEY, text(extend))
    cached = _home_cache.get(cache_key)
    if cached and cached[0] > time.time():
        return cached[1]
    data = cms('nav', {'token': ''})
    classes = []
    filters = {}
    for item in list_of(data.get('list')):
        if not isinstance(item, dict):
            continue
        if item.get('type_id') is None or not text(item.get('type_name')):
            continue
        tid = text(item['type_id'])
        classes.append({'type_id': tid, 'type_name': text(item['type_name'])})
        ext = object_of(item.get('type_extend'))
        groups = []
        for key, name in FILTER_NAMES.items():
            values = [v for v in (text(x) for x in text(ext.get(key)).split(',')) if v]
            values = list(dict.fromkeys(values))
            if values:
                groups.append({
                    'key': key,
                    'name': name,
                    'init': '',
                    'value': [{'n': '全部', 'v': ''}] + [{'n': v, 'v': v} for v in values],
                })
        if groups:
            filters[tid] = groups
    result = {'class': classes, 'filters': filters}
    if classes:
        _home_cache[cache_key] = (time.time() + HOME_CACHE_TTL, result)
    return result


def home_vod():
    data = cms('index_video', {'token': ''})
    vlist = []
    for item in list_of(data.get('list')):
        if isinstance(item, dict):
            vlist.extend(list_of(item.get('vlist')))
    return {'list': vlist}


def paginated(data, requested_page):
    lst = list_of(data.get('list'))
    raw_page = data.get('page')
    page = page_of(raw_page if raw_page is not None else requested_page)
    try:
        limit = int(data.get('limit') or 0)
    except (TypeError, ValueError):
        limit = 0
    if limit <= 0:
        limit = PAGE_LIMIT
    try:
        raw_pagecount = int(data.get('pagecount') or 0)
    except (TypeError, ValueError):
        raw_pagecount = 0
    has_pagecount = raw_pagecount > 0
    pagecount = raw_pagecount if has_pagecount else page + (1 if len(lst) >= limit else 0)
    try:
        raw_total = data.get('total')
        has_total = raw_total is not None and int(raw_total) >= 0
    except (TypeError, ValueError):
        has_total = False
    if has_pagecount and has_total:
        total = int(data.get('total'))
    else:
        total = (page - 1) * limit + len(lst) + (1 if pagecount > page else 0)
    data['page'] = page
    data['pagecount'] = pagecount
    data['limit'] = limit
    data['total'] = total
    data['list'] = lst
    return data


def category(tid, pg, extend):
    page = page_of(pg)
    tid = text(tid)
    if not tid:
        return paginated({'list': []}, page)
    extend = extend if isinstance(extend, dict) else {}
    params = {'tid': tid, 'pg': str(page), 'limit': '18'}
    for key in FILTER_NAMES:
        value = text(extend.get(key))
        if value and value != 'all':
            params[key] = value
    return paginated(cms('video', params), page)


# 已知失效的直链域名（实测 404），列在播放列表时直接剔除
DEAD_HOSTS = ('ym4kjx.lyyytv.cn',)


def playlist(value):
    parts = []
    for entry in text(value).split('#'):
        sep = entry.find('$')
        if sep <= 0 or not text(entry[sep + 1:]):
            continue
        url = decrypt_lvdou(entry[sep + 1:])
        # 【已解除所有域名屏蔽，强制放行所有网盘线路】
        parts.append('%s$%s' % (text(entry[:sep]), url))
    return '#'.join(parts)


def detail(ids):
    if not isinstance(ids, (list, tuple)):
        ids = [ids]
    lst = []
    for vid in ids:
        vid = text(vid)
        if not vid:
            continue
        data = cms('video_detail', {'id': vid}).get('data')
        if not isinstance(data, dict):
            continue
        players = data.get('vod_url_with_player')
        vod = {k: v for k, v in data.items() if k != 'vod_url_with_player'}
        names = text(vod.get('vod_play_from')).split('$$$')
        if isinstance(players, list):
            sources = players
        else:
            sources = [
                {'name': names[i] if i < len(names) else '', 'url': u}
                for i, u in enumerate(text(vod.get('vod_play_url')).split('$$$'))
            ]
        froms = []
        urls = []
        for index, source in enumerate(sources):
            if not isinstance(source, dict):
                continue
            url = playlist(source.get('url'))
            if not url:
                continue
            name = text(source.get('name')) or text(source.get('code')) or '线路%d' % (index + 1)
            froms.append(re.sub(r'[$#]', ' ', name))
            urls.append(url)
        vod['vod_play_from'] = '$$$'.join(froms)
        vod['vod_play_url'] = '$$$'.join(urls)
        lst.append(vod)
    return {'list': lst}


def search(key, pg):
    wd = text(key)
    page = page_of(pg)
    if not wd:
        return paginated({'list': []}, page)
    data = cms('search', {'text': wd, 'pg': str(page)})
    lst = []
    for item in list_of(data.get('list')):
        if isinstance(item, dict):
            lst.append({k: v for k, v in item.items() if k != 'type'})
    data['list'] = lst
    return paginated(data, page)


def play(play_id):
    """对齐 JS play：无条件走解析接口，解出真实地址再交播放器。"""
    original = decrypt_lvdou(play_id)
    if not original:
        return {'parse': 0, 'url': '', 'header': dict(PARSE_HEADERS)}

    # 兼容老加密：ldmax 前缀先本地解密
    if is_ldmax_url(original):
        decrypted = decrypt_ldmax(original)
        if decrypted:
            original = decrypted

    # 明文 mp4/m3u8 直链：不经解析，直接交给播放器
    if is_media_url(original):
        return {'parse': 0, 'url': original, 'header': dict(PARSE_HEADERS)}

    # 解析结果缓存
    now = time.time()
    cached = _play_cache.get(original)
    if cached and cached[0] > now:
        return {'parse': 0, 'url': cached[1], 'header': dict(PARSE_HEADERS)}

    resolved = parse_url(original)
    if resolved:
        _play_cache[original] = (now + PLAY_CACHE_TTL, resolved)

    # 解析失败：回退原地址，至少给播放器一个可尝试的目标
    return {'parse': 0, 'url': resolved or original, 'header': dict(PARSE_HEADERS)}


class Spider(Spider):
    def getName(self):
        return '🎬 影探4K'

    def init(self, extend=''):
        self.extend = extend or ''

    def isVideoFormat(self, url):
        return is_media_url(url)

    def manualVideoCheck(self):
        return False

    def homeContent(self, filter):
        return home(self.extend)

    def homeVideoContent(self):
        return home_vod()

    def categoryContent(self, tid, pg, filter, extend):
        return category(tid, pg, extend)

    def detailContent(self, ids):
        return detail(ids)

    def searchContent(self, key, quick, pg='1'):
        return search(key, pg)

    def playerContent(self, flag, id, vipFlags):
        return play(id)

    def localProxy(self, param):
        return None

    def destroy(self):
        pass