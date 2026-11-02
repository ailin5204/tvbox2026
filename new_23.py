#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""听友音乐（tingyou.fm「听歌」栏目）TVBox Python 源。

与听书源相互独立：只使用 /api/web/v1/tv/call 音乐接口。
该接口的请求/响应都是 AES-256-CBC(PKCS7) + Base64，并用 HMAC-SHA256 签名，
密钥写在站点前端 JS 里，这里做了纯 Python 实现，不依赖 cryptography。

已适配：
- 音乐分区：热歌 / 新歌 / 歌手 / 榜单 / 歌单
- 专辑列表、专辑详情、曲目列表、跨分区搜索
- 单曲搜索：本地曲库 + 命中专辑反查，结果直接是单曲
- 标题漏字兜底：如「雨后的风景」也能命中「雨过后的风景」
- 播放：music.playback_session 换取带时效签名的直链（MP3）
- 歌词：音频自带 ID3 USLT（LRC），按 Range 读文件头解析后随 lrc / vod_lyric 返回
- 游客身份按需注册，播放请求 401 时自动重新注册并重试

说明：站点接口本身没有「按歌名搜曲目」的 operation，music.albums 的 q
只匹配专辑/歌单标题。因此单曲搜索由本脚本完成：
1. 启动时后台抓曲目建纯内存索引，不写任何文件、不落盘，进程退出即释放；
   先抓「热歌」（约 1 万首，通常几十秒），再补两页「歌单」（经典老歌多），
   然后「榜单」，最后继续扩歌单到 40 页、约 8 万首（上限 12 万首）；
   AES 解密用查表实现，比逐字节实现快 50 倍以上；
2. 搜索时先查索引，再对接口命中的「歌手/歌单」专辑抓曲目做二次过滤，
   反查到的曲目会并入索引；
3. 单曲结果用 track:<album_id>:<index> 作为 vod_id，点开即整首播放。

局限：全站曲目约 1200 万首（歌单分区），纯内存不可能全量建库，
因此冷门歌仍可能搜不到；索引建完前结果偏少。
建库速度取决于盒子的 CPU 和网络，热歌索引可用通常在 1 分钟内。
"""

import html
import hmac
import http.client
import hashlib
import json
import re
import ssl
import threading
import time
import urllib.error
import urllib.request
from urllib.parse import urlsplit
import uuid

try:
    from base.spider import Spider as BaseSpider
except ImportError:
    class BaseSpider:
        """本地/离线调试用的最小实现"""

        def fetch(self, url, headers=None, data=None, timeout=15):
            req = urllib.request.Request(url, data=data, headers=headers or {})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                body = resp.read()

                class R:
                    text = body.decode("utf-8", errors="ignore")
                    content = body
                    status_code = resp.status

                return R()


SITE_URL = "https://www.tingyou.fm"
# 站点同域代理优先，失败时走直连 API 主机
API_BASES = (
    SITE_URL + "/api",
    "https://appp.fdhtbz.cn/api",
    "https://laopaoaappi.oobyvy.vip/api",
)

UA = ("Mozilla/5.0 (Linux; Android 10; Mobile) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36")

BASE_HEADERS = {
    "User-Agent": UA,
    "Accept": "application/json, text/plain, */*",
    "Content-Type": "application/x-www-form-urlencoded",
    "Referer": SITE_URL + "/",
    "Origin": SITE_URL,
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "cross-site",
}
PLAY_HEADERS = {
    "User-Agent": UA,
    "Referer": SITE_URL + "/",
}
DEFAULT_COVER = SITE_URL + "/_nuxt/cover-placeholder.Bbph-p4m.webp"

# 前端 bundle 中的固定密钥（AES-256-CBC + HMAC-SHA256）
AES_KEY = bytes.fromhex(
    "11059a4c989dd9d4837778b013d164baa0ad4d7b0076e722369f6f085814293f")
AES_IV = bytes.fromhex("dd3ea319024c649d2ebcd1bda551a307")
SIGN_KEY = bytes.fromhex("51c5b55800a7efd1")

SECTIONS = (
    ("hot", "热歌"),
    ("new", "新歌"),
    ("artist", "歌手"),
    ("ranking", "榜单"),
    ("playlist", "歌单"),
)
SECTION_NAMES = dict(SECTIONS)
SECTION_IDS = {key for key, _ in SECTIONS}

LIST_PAGE_SIZE = 30
SEARCH_PAGE_SIZE = 30
MAX_TRACKS = 5000
REQUEST_TIMEOUT = 20
TOKEN_TTL = 12 * 3600

# ---------- 单曲索引 ----------
INDEX_DEEP_SECTION = "playlist"       # 热歌/榜单之后继续补歌单，覆盖经典老歌
INDEX_DEEP_PAGES = 40                 # 每页 30 张歌单，最多 1200 张
INDEX_DEEP_TRACK_LIMIT = 120000       # 内存上限，约 70MB
INDEX_PAGE_SIZE = 100
INDEX_WORKERS = 4
INDEX_SCAN_ALBUMS = 10                 # 搜索时反查的专辑数
INDEX_SCAN_ALBUMS_QUICK = 3
INDEX_SCAN_WORKERS = 4
INDEX_SCAN_MIN = 12                    # 普通搜索索引结果少于该数时反查
INDEX_SCAN_MIN_QUICK = 30              # quick 搜索更保守，避免拖慢联想
INDEX_SCAN_WAIT = 6.0                  # 反查专辑的超时秒数
INDEX_WAIT_FULL = 2.5                  # 普通搜索等索引的秒数
INDEX_WAIT_QUICK = 0.4                 # quick 首轮搜索等索引的秒数
INDEX_SOURCE_TAG = "单曲"


# ==================== 纯 Python AES-256-CBC ====================
# 只保留本项目用得到的加密/解密；已用 NIST 标准向量验证。

_SBOX = (
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
)
_INV_SBOX = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV_SBOX[_v] = _i
_RCON = (0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36)


def _xtime(a):
    a <<= 1
    return (a ^ 0x11b) & 0xff if a & 0x100 else a


def _gmul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a = _xtime(a)
        b >>= 1
    return result


def _expand_key(key):
    nk = len(key) // 4
    rounds = nk + 6
    words = [list(key[4 * i:4 * i + 4]) for i in range(nk)]
    for i in range(nk, 4 * (rounds + 1)):
        temp = list(words[i - 1])
        if i % nk == 0:
            temp = temp[1:] + temp[:1]
            temp = [_SBOX[b] for b in temp]
            temp[0] ^= _RCON[i // nk - 1]
        elif nk > 6 and i % nk == 4:
            temp = [_SBOX[b] for b in temp]
        words.append([words[i - nk][j] ^ temp[j] for j in range(4)])
    return words, rounds


# ---- 解密加速：T 表 ----
# 原来的逐字节 _gmul 在电视盒子上解一个 30KB 响应要好几秒，
# 这里预先算出 T 表，每块只做查表 + 异或，实测快 50 倍以上。

def _mul_table(factor):
    return bytes(_gmul(value, factor) for value in range(256))


_M9 = _mul_table(9)
_M11 = _mul_table(11)
_M13 = _mul_table(13)
_M14 = _mul_table(14)

_TD0 = [0] * 256
_TD1 = [0] * 256
_TD2 = [0] * 256
_TD3 = [0] * 256
_TD4 = [0] * 256
for _x in range(256):
    _s = _INV_SBOX[_x]
    _w = ((_M14[_s] << 24) | (_M9[_s] << 16)
          | (_M13[_s] << 8) | _M11[_s])
    _TD0[_x] = _w
    _TD1[_x] = ((_w >> 8) | (_w << 24)) & 0xffffffff
    _TD2[_x] = ((_w >> 16) | (_w << 16)) & 0xffffffff
    _TD3[_x] = ((_w >> 24) | (_w << 8)) & 0xffffffff
    _TD4[_x] = _s


def _inv_mix_word(word):
    a0 = (word >> 24) & 0xff
    a1 = (word >> 16) & 0xff
    a2 = (word >> 8) & 0xff
    a3 = word & 0xff
    return (((_M14[a0] ^ _M11[a1] ^ _M13[a2] ^ _M9[a3]) << 24)
            | ((_M9[a0] ^ _M14[a1] ^ _M11[a2] ^ _M13[a3]) << 16)
            | ((_M13[a0] ^ _M9[a1] ^ _M14[a2] ^ _M11[a3]) << 8)
            | (_M11[a0] ^ _M13[a1] ^ _M9[a2] ^ _M14[a3]))


def _word_of(values):
    return ((values[0] << 24) | (values[1] << 16)
            | (values[2] << 8) | values[3])


def _decrypt_key(words, rounds):
    """等价逆密码的轮密钥：首尾不变，中间做 InvMixColumns。"""
    key = [0] * (4 * (rounds + 1))
    for col in range(4):
        key[col] = _word_of(words[col])
        key[4 * rounds + col] = _word_of(words[4 * rounds + col])
    for rnd in range(1, rounds):
        for col in range(4):
            key[4 * rnd + col] = _inv_mix_word(_word_of(words[4 * rnd + col]))
    return key


def _decrypt_block_int(block, key, rounds):
    s0 = int.from_bytes(block[0:4], "big") ^ key[4 * rounds]
    s1 = int.from_bytes(block[4:8], "big") ^ key[4 * rounds + 1]
    s2 = int.from_bytes(block[8:12], "big") ^ key[4 * rounds + 2]
    s3 = int.from_bytes(block[12:16], "big") ^ key[4 * rounds + 3]
    for rnd in range(rounds - 1, 0, -1):
        base = 4 * rnd
        t0 = (_TD0[(s0 >> 24) & 0xff] ^ _TD1[(s3 >> 16) & 0xff]
              ^ _TD2[(s2 >> 8) & 0xff] ^ _TD3[s1 & 0xff] ^ key[base])
        t1 = (_TD0[(s1 >> 24) & 0xff] ^ _TD1[(s0 >> 16) & 0xff]
              ^ _TD2[(s3 >> 8) & 0xff] ^ _TD3[s2 & 0xff] ^ key[base + 1])
        t2 = (_TD0[(s2 >> 24) & 0xff] ^ _TD1[(s1 >> 16) & 0xff]
              ^ _TD2[(s0 >> 8) & 0xff] ^ _TD3[s3 & 0xff] ^ key[base + 2])
        t3 = (_TD0[(s3 >> 24) & 0xff] ^ _TD1[(s2 >> 16) & 0xff]
              ^ _TD2[(s1 >> 8) & 0xff] ^ _TD3[s0 & 0xff] ^ key[base + 3])
        s0, s1, s2, s3 = t0, t1, t2, t3
    t0 = (((_TD4[(s0 >> 24) & 0xff] << 24)
           | (_TD4[(s3 >> 16) & 0xff] << 16)
           | (_TD4[(s2 >> 8) & 0xff] << 8)
           | _TD4[s1 & 0xff]) ^ key[0])
    t1 = (((_TD4[(s1 >> 24) & 0xff] << 24)
           | (_TD4[(s0 >> 16) & 0xff] << 16)
           | (_TD4[(s3 >> 8) & 0xff] << 8)
           | _TD4[s2 & 0xff]) ^ key[1])
    t2 = (((_TD4[(s2 >> 24) & 0xff] << 24)
           | (_TD4[(s1 >> 16) & 0xff] << 16)
           | (_TD4[(s0 >> 8) & 0xff] << 8)
           | _TD4[s3 & 0xff]) ^ key[2])
    t3 = (((_TD4[(s3 >> 24) & 0xff] << 24)
           | (_TD4[(s2 >> 16) & 0xff] << 16)
           | (_TD4[(s1 >> 8) & 0xff] << 8)
           | _TD4[s0 & 0xff]) ^ key[3])
    return (t0 << 96) | (t1 << 64) | (t2 << 32) | t3


def _add_round_key(state, words, rnd):
    for col in range(4):
        for row in range(4):
            state[row + 4 * col] ^= words[4 * rnd + col][row]


def _encrypt_block(block, words, rounds):
    state = list(block)
    _add_round_key(state, words, 0)
    for rnd in range(1, rounds):
        state = [_SBOX[b] for b in state]
        state = [state[(i + 4 * (i % 4)) % 16] for i in range(16)]
        source = list(state)
        for col in range(4):
            a0, a1, a2, a3 = source[4 * col:4 * col + 4]
            state[4 * col] = _gmul(a0, 2) ^ _gmul(a1, 3) ^ a2 ^ a3
            state[4 * col + 1] = a0 ^ _gmul(a1, 2) ^ _gmul(a2, 3) ^ a3
            state[4 * col + 2] = a0 ^ a1 ^ _gmul(a2, 2) ^ _gmul(a3, 3)
            state[4 * col + 3] = _gmul(a0, 3) ^ a1 ^ a2 ^ _gmul(a3, 2)
        _add_round_key(state, words, rnd)
    state = [_SBOX[b] for b in state]
    state = [state[(i + 4 * (i % 4)) % 16] for i in range(16)]
    _add_round_key(state, words, rounds)
    return bytes(state)


class _AES256CBC:
    """AES-256-CBC + PKCS#7（纯 Python T 表实现，不依赖任何 C 库）。"""

    def __init__(self, key, iv):
        self.iv = iv
        self._words, self._rounds = _expand_key(key)
        self._dkey = _decrypt_key(self._words, self._rounds)

    def encrypt(self, data):
        pad = 16 - len(data) % 16
        data = data + bytes([pad]) * pad
        out = bytearray()
        prev = self.iv
        for i in range(0, len(data), 16):
            block = bytes(a ^ b for a, b in zip(data[i:i + 16], prev))
            prev = _encrypt_block(block, self._words, self._rounds)
            out += prev
        return bytes(out)

    def decrypt(self, data):
        if not data or len(data) % 16:
            raise ValueError("ciphertext length invalid")
        out = bytearray(len(data))
        prev = int.from_bytes(self.iv, "big")
        key = self._dkey
        rounds = self._rounds
        for i in range(0, len(data), 16):
            block = data[i:i + 16]
            current = int.from_bytes(block, "big")
            value = _decrypt_block_int(block, key, rounds) ^ prev
            out[i:i + 16] = value.to_bytes(16, "big")
            prev = current
        plain = bytes(out)
        pad = plain[-1]
        if not 1 <= pad <= 16 or plain[-pad:] != bytes([pad]) * pad:
            raise ValueError("bad PKCS#7 padding")
        return plain[:-pad]


def _b64(data):
    import base64
    return base64.b64encode(data).decode("ascii")


def _unb64(text):
    import base64
    return base64.b64decode(re.sub(r"\s+", "", text or ""))


# ==================== 爬虫 ====================


# ---------- HTTP 长连接 ----------
# 每个线程复用一个连接，省掉每次请求的 TCP/TLS 握手；
# 电视盒子的 ARM CPU 做 TLS 握手很贵，这一步能明显加快建库。

_SSL_CONTEXT = None
_POOL = threading.local()


def _pooled_post(url, headers, body):
    global _SSL_CONTEXT
    parsed = urlsplit(url)
    scheme = (parsed.scheme or "").lower()
    host = parsed.hostname
    if scheme not in ("http", "https") or not host:
        return None
    port = parsed.port or (443 if scheme == "https" else 80)
    path = parsed.path or "/"
    if parsed.query:
        path += "?" + parsed.query
    key = (scheme, host, port)
    conn = getattr(_POOL, "conn", None)
    if conn is None or getattr(_POOL, "key", None) != key:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass
        try:
            if scheme == "https":
                if _SSL_CONTEXT is None:
                    _SSL_CONTEXT = ssl.create_default_context()
                conn = http.client.HTTPSConnection(
                    host, port, timeout=REQUEST_TIMEOUT, context=_SSL_CONTEXT)
            else:
                conn = http.client.HTTPConnection(
                    host, port, timeout=REQUEST_TIMEOUT)
        except Exception:
            _POOL.conn = None
            return None
        _POOL.conn = conn
        _POOL.key = key
    try:
        conn.request("POST", path, body=body, headers=headers)
        response = conn.getresponse()
        data = response.read()
        if response.will_close:
            conn.close()
            _POOL.conn = None
        return data.decode("utf-8", errors="ignore")
    except Exception:
        try:
            conn.close()
        except Exception:
            pass
        _POOL.conn = None
        return None


# ---------- MP3 内嵌歌词 ----------
# 站点接口没有歌词，但音频文件带了 ID3 USLT（LRC 文本），
# 用 Range 只取文件头解析，壳子的音乐面板认 lrc / vod_lyric 字段。

_LRC_META = re.compile(
    r"^\[(ti|ar|al|by|offset|kuwo|ver|re|ve|length|kana|language):", re.I)


def _syncsafe4(raw):
    return (((raw[0] & 0x7f) << 21) | ((raw[1] & 0x7f) << 14)
            | ((raw[2] & 0x7f) << 7) | (raw[3] & 0x7f))


def _decode_uslt(payload):
    """USLT：编码(1) + 语言(3) + 描述(0结尾) + 歌词。"""
    if len(payload) < 5:
        return ""
    enc = payload[0]
    raw = payload[4:]
    if enc == 0:
        try:
            text = raw.decode("gbk")
        except Exception:
            text = raw.decode("latin-1", "ignore")
    elif enc == 1:
        try:
            text = raw.decode("utf-16")
        except Exception:
            try:
                text = raw.decode("utf-16-le")
            except Exception:
                text = raw.decode("utf-16-be", "ignore")
    elif enc == 2:
        text = raw.decode("utf-16-be", "ignore")
    else:
        text = raw.decode("utf-8", "ignore")
    text = text.replace("\ufeff", "")
    return text.split("\x00", 1)[-1].strip("\x00 \r\n\t")


def _parse_id3_lyrics(buf):
    if len(buf) < 10 or buf[:3] != b"ID3":
        return ""
    ver = buf[3]
    flags = buf[5]
    body = buf[10:10 + _syncsafe4(buf[6:10])]
    if flags & 0x80:
        body = body.replace(b"\xff\x00", b"\xff")
    pos = 0
    if flags & 0x40 and len(body) >= 4:
        pos = (_syncsafe4(body[:4]) if ver >= 4
               else 4 + int.from_bytes(body[:4], "big"))
    while pos + 10 <= len(body):
        fid = body[pos:pos + 4]
        if not re.match(rb"^[A-Z0-9]{4}$", fid):
            break
        size = (_syncsafe4(body[pos + 4:pos + 8]) if ver >= 4
                else int.from_bytes(body[pos + 4:pos + 8], "big"))
        if pos + 10 + size > len(body):
            break
        fflags = body[pos + 8:pos + 10]
        bad = (fflags[0] & 0x4c) if ver >= 4 else (fflags[0] & 0xc0)
        if not bad and fid == b"USLT":
            text = _decode_uslt(body[pos + 10:pos + 10 + size])
            if text:
                return text
        pos += 10 + size
    return ""


def _clean_lrc(text):
    """去掉 [ti:]/[kuwo:] 这类元信息，只留时间轴和正文。"""
    lines = []
    for line in (text or "").replace("\r", "").split("\n"):
        line = line.strip()
        if not line or _LRC_META.match(line):
            continue
        lines.append(line)
    return "\n".join(lines)[:20000]


def _range_head(url, end):
    req = urllib.request.Request(url, headers=dict(
        PLAY_HEADERS, Range="bytes=0-%d" % end))
    with urllib.request.urlopen(req, timeout=3) as resp:
        return resp.read(2 * 1024 * 1024)


def _embedded_lyrics(url):
    try:
        data = _range_head(url, 8191)
        text = _parse_id3_lyrics(data)
        if not text and len(data) >= 10 and data[:3] == b"ID3":
            need = _syncsafe4(data[6:10]) + 10
            if need > len(data):
                text = _parse_id3_lyrics(_range_head(url, need - 1))
        return _clean_lrc(text)
    except Exception:
        return ""


class Spider(BaseSpider):
    _token = ""
    _token_time = 0.0
    _device_id = ""
    _identity_lock = threading.Lock()

    # 单曲索引（进程内共享；构建完成后常驻，绝不落盘）
    _index_lock = threading.Lock()
    _index_tracks = []            # [(title, artist, album, album_id, index), ...]
    _index_strings = {}           # 字符串驻留，降低内存占用
    _index_deep_page = 1          # 歌单分区已抓到的页码
    _index_ready = threading.Event()
    _index_started = False

    # 歌词缓存（只存内存，最多 128 首）
    _lyric_cache = {}

    # ---------- TVBox 生命周期 ----------

    def init(self, extend=""):
        self._ext = self._as_dict(extend)
        self._base = str(self._ext.get("api_base") or "").rstrip("/")
        if not self._base and isinstance(extend, str) and extend.strip().startswith("http"):
            self._base = extend.strip().rstrip("/")
        self._cipher = _AES256CBC(AES_KEY, AES_IV)
        with Spider._identity_lock:
            if not Spider._device_id:
                Spider._device_id = str(uuid.uuid4())
            self._device_id = Spider._device_id
            self._token = Spider._token
        self._start_track_index()

    def getName(self):
        return "tingyou-music"

    def isVideoFormat(self, url):
        return any(ext in (url or "").lower()
                   for ext in (".mp3", ".m4a", ".aac", ".flac", ".ogg", ".wav"))

    def manualVideoCheck(self):
        return False

    def homeContent(self, filter=False):
        result = {
            "class": [{"type_id": key, "type_name": name}
                      for key, name in SECTIONS],
        }
        if filter:
            result["filters"] = {}
        return result

    def homeVideoContent(self):
        try:
            return {"list": self.categoryContent("hot", "1").get("list") or []}
        except Exception:
            return {"list": []}

    def categoryContent(self, tid, pg, filter=False, extend=None):
        section = str(tid or "").strip()
        if section not in SECTION_IDS:
            section = "hot"
        page = max(1, self._to_int(pg, 1))
        try:
            data = self._music_albums(section, page) or {}
        except Exception:
            return {"list": [], "page": page, "pagecount": 1,
                    "limit": LIST_PAGE_SIZE, "total": 0}

        items = data.get("items") or []
        total = self._to_int(data.get("total"), 0)
        has_more = data.get("has_more")
        if not isinstance(has_more, bool):
            has_more = len(items) >= LIST_PAGE_SIZE
        pagecount = self._pagecount(total, LIST_PAGE_SIZE, page, has_more)
        return {
            "list": [v for v in (self._album_to_vod(it) for it in items) if v],
            "page": page,
            "pagecount": pagecount,
            "limit": LIST_PAGE_SIZE,
            "total": total or len(items),
        }

    def searchContent(self, key, quick=False, pg="1"):
        keyword = (key or "").strip()
        page = max(1, self._to_int(pg, 1))
        empty = {"list": [], "page": page, "pagecount": 1,
                 "limit": SEARCH_PAGE_SIZE, "total": 0}
        if not keyword:
            return empty

        results, total, has_more, hits = self._search_all(keyword, page)

        # 「周杰伦 稻香」这类多个关键词，接口按整串匹配会查不到；
        # 此时退化为逐个关键词搜索，尽量给出可用的结果。
        tokens = []
        if re.search(r"\s", keyword):
            tokens = [part for part in re.split(r"\s+", keyword) if len(part) >= 2][:3]
            if not results and tokens:
                merged, seen = [], set()
                for token in tokens:
                    sub, sub_total, sub_more, sub_hits = self._search_all(token, page)
                    total = max(total, sub_total)
                    has_more = has_more or sub_more
                    hits.extend(sub_hits)
                    for vod in sub:
                        if vod["vod_id"] not in seen:
                            seen.add(vod["vod_id"])
                            merged.append(vod)
                results = merged

        # 单曲：先查本地曲库，再对命中专辑做一次曲目反查
        self._wait_index(INDEX_WAIT_QUICK if quick else INDEX_WAIT_FULL)
        tracks = self._dedupe_tracks(self._index_search(keyword, tokens))
        min_tracks = INDEX_SCAN_MIN_QUICK if quick else INDEX_SCAN_MIN
        if hits and len(tracks) < min_tracks:
            if quick:
                # 曲库还冷时 quick 也补一点，热了就只靠索引，避免拖慢联想
                budget = (INDEX_SCAN_ALBUMS_QUICK
                          if self._index_size() < 6000 else 0)
            else:
                budget = INDEX_SCAN_ALBUMS if page <= 1 else 3
            if budget:
                tracks.extend(self._scan_album_tracks(
                    hits, keyword, budget, INDEX_SCAN_WAIT))
        tracks = self._dedupe_tracks(tracks)

        # 分页：单曲也按页切，避免第 2 页重复第 1 页的单曲
        offset = (page - 1) * SEARCH_PAGE_SIZE
        track_page = tracks[offset:offset + SEARCH_PAGE_SIZE]
        if track_page:
            # 有单曲时把专辑/歌单压缩到 10 条，避免满屏合集
            results = results[:10]
        merged = self._dedupe_vods(track_page + results)

        pagecount = self._pagecount(
            (total or len(results)) + len(tracks),
            SEARCH_PAGE_SIZE, page,
            has_more or len(tracks) > page * SEARCH_PAGE_SIZE)
        return {
            "list": merged[:SEARCH_PAGE_SIZE * 2],
            "page": page,
            "pagecount": pagecount,
            "limit": SEARCH_PAGE_SIZE,
            "total": (total or len(results)) + len(tracks),
        }

    def _search_all(self, keyword, page):
        """并发查询 5 个分区，按站点顺序去重。返回 (专辑结果, 总数, 有下一页, 原始命中)。"""
        found = {}
        lock = threading.Lock()
        totals, has_more = [], []

        def worker(section):
            try:
                data = self._music_albums(section, page, keyword) or {}
            except Exception:
                return
            with lock:
                found[section] = data
                totals.append(self._to_int(data.get("total"), 0))
                has_more.append(bool(data.get("has_more")))

        threads = [threading.Thread(target=worker, args=(section,), daemon=True)
                   for section, _ in SECTIONS]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(7)

        results, seen, hits = [], set(), []
        for section, _ in SECTIONS:
            data = found.get(section)
            if not data:
                continue
            for item in data.get("items") or []:
                hits.append((section, item))
                vod = self._album_to_vod(item)
                if vod and vod["vod_id"] not in seen:
                    seen.add(vod["vod_id"])
                    results.append(vod)

        return (results,
                max(totals) if totals else len(results),
                any(has_more),
                hits)

    def detailContent(self, ids):
        vid = ids[0] if isinstance(ids, (list, tuple)) and ids else ids
        value = str(vid or "").strip()
        if value.startswith("track:"):
            return self._track_detail(value)
        album_id = self._album_id(vid)
        if not album_id:
            return {"list": []}

        album = {}
        try:
            album_result = self._call("music.album", {"album_id": album_id}) or {}
            if isinstance(album_result.get("data"), dict):
                album = album_result["data"]
        except Exception:
            album = {}

        chapters = []
        try:
            tracks = self._call("music.tracks", {"album_id": album_id}) or {}
            if isinstance(tracks.get("data"), dict):
                chapters = tracks["data"].get("chapters") or []
        except Exception:
            chapters = []

        title = (self._clean(album.get("title"))
                 or "音乐专辑")
        artist = (self._clean(album.get("author") or album.get("teller"))
                  or (self._clean(chapters[0].get("artist")) if chapters else ""))

        episodes, seen = [], set()
        chapters.sort(key=lambda track: self._to_int(track.get("index"), 0))
        for track in chapters:
            index = self._to_int(track.get("index"), 0)
            if index <= 0 or index in seen:
                continue
            seen.add(index)
            name = self._clean(track.get("title")) or "第%d首" % index
            singer = self._clean(track.get("artist"))
            label = "%02d. %s" % (index, name)
            if singer:
                label += " - " + singer
            episodes.append("%s$play/%s/%d" % (label, album_id, index))
            if len(episodes) >= MAX_TRACKS:
                break

        total = self._to_int(album.get("count"), 0) or len(episodes)
        section = str(album.get("section") or "")
        remarks = "%d首" % total
        if section in SECTION_NAMES:
            remarks += " · " + SECTION_NAMES[section]

        notes = []
        synopsis = self._clean(album.get("synopsis") or album.get("description")
                               or album.get("intro"))
        if synopsis:
            notes.append(synopsis)
        if artist:
            notes.append("歌手/创建者：" + artist)
        if section in SECTION_NAMES:
            notes.append("分区：" + SECTION_NAMES[section])
        if total:
            notes.append("共 %d 首" % total)
        if not episodes:
            notes.append("该专辑暂未提供可播放曲目。")

        vod = {
            "vod_id": "music:" + album_id,
            "vod_name": title,
            "vod_pic": self._img(album.get("cover_url") or DEFAULT_COVER),
            "vod_actor": artist,
            "vod_director": self._clean(album.get("teller")),
            "vod_content": "\n".join(notes),
            "vod_remarks": remarks,
            "vod_play_from": "听友音乐",
            "vod_play_url": "#".join(episodes),
        }
        return {"list": [vod]}

    def playerContent(self, flag, id, vipFlags=None):
        value = (id or "").strip()
        if value.startswith("//"):
            value = "https:" + value
        if value.startswith("http"):
            return {"parse": 0, "url": value,
                    "header": dict(PLAY_HEADERS), "jx": 0}

        match = re.match(r"^play/([0-9A-Za-z-]+)/(\d+)$", value)
        if not match:
            return {"parse": 0, "msg": "无效的播放标识"}

        album_id, index = match.group(1), int(match.group(2))
        try:
            result = self._playback(album_id, index)
        except Exception:
            return {"parse": 0, "msg": "播放地址获取失败"}

        if self._to_int(result.get("code"), 0) != 200:
            message = self._clean(result.get("message") or result.get("msg"))
            return {"parse": 0, "msg": message or "播放地址获取失败"}

        data = result.get("data") or {}
        url = self._img(data.get("play_url"))
        if not url:
            return {"parse": 0, "msg": "播放地址为空，可能已下架"}
        lyric = self._lyrics_for(album_id, index, url)
        return {"parse": 0, "url": url,
                "header": dict(PLAY_HEADERS), "jx": 0,
                "lrc": lyric, "vod_lyric": lyric}

    def _lyrics_for(self, album_id, index, url):
        key = "%s:%s" % (album_id, index)
        cached = Spider._lyric_cache.get(key)
        if cached is not None:
            return cached
        text = _embedded_lyrics(url)
        if text:
            if len(Spider._lyric_cache) >= 128:
                Spider._lyric_cache.clear()
            Spider._lyric_cache[key] = text
        return text

    # ---------- 音乐接口 ----------

    def _music_albums(self, section, page, keyword="", page_size=None):
        size = page_size or LIST_PAGE_SIZE
        query = {"section": section, "page": str(page),
                 "page_size": str(size)}
        if keyword:
            query["q"] = keyword
        data = self._call("music.albums", {}, query) or {}
        if data.get("code") not in (None, 200):
            raise RuntimeError(str(data.get("message") or "music.albums failed"))
        payload = data.get("data")
        if not isinstance(payload, dict):
            payload = data if isinstance(data, dict) else {}
        if isinstance(payload.get("data"), dict):
            payload = payload["data"]
        return payload

    def _playback(self, album_id, index):
        payload = self._call(
            "music.playback_session",
            {"album_id": album_id, "index": str(index)},
            {},
            idempotency_key="web-music-" + uuid.uuid4().hex,
            token=True)
        return payload or {}

    def _call(self, operation, params=None, query=None,
              idempotency_key=None, token=False, allow_retry=True):
        if token:
            self._ensure_token()
        body_obj = {
            "operation": operation,
            "params": params or {},
            "query": query or {},
        }
        if idempotency_key:
            body_obj["idempotency_key"] = idempotency_key
        result = self._post_secure(body_obj, self._token if token else "")
        code = self._to_int(result.get("code"), 0)
        if token and allow_retry and code in (401, 403):
            self._reset_identity()
            self._ensure_token()
            result = self._post_secure(body_obj, self._token)
        return result

    def _post_secure(self, body_obj, access_token):
        obj = dict(body_obj)
        obj.update(self._identity())
        plain = json.dumps(obj, ensure_ascii=False, separators=(",", ":"))
        encrypted = _b64(self._cipher.encrypt(plain.encode("utf-8")))
        signature = _b64(hmac.new(SIGN_KEY, encrypted.encode("ascii"),
                                  hashlib.sha256).digest())

        headers = dict(BASE_HEADERS)
        headers["X-Post-Signature"] = signature
        headers["X-Device-Id"] = self._device_id
        if access_token:
            headers["Authorization"] = "Bearer " + access_token

        last_error = None
        fallback = None
        for base in self._candidate_bases():
            try:
                text = self._fetch_text(
                    base + "/web/v1/tv/call", headers,
                    encrypted.encode("utf-8"))
                if not text:
                    continue
                result = json.loads(self._cipher.decrypt(_unb64(text)).decode("utf-8"))
                if not isinstance(result, dict):
                    continue
                code = self._to_int(result.get("code"), 0)
                if code == 429 or code >= 500:
                    # 当前线路被限流/故障，换下一个线路再试
                    fallback = result
                    continue
                self._base = base
                return result
            except Exception as error:
                last_error = error
        if fallback is not None:
            return fallback
        if last_error:
            raise last_error
        raise RuntimeError("music api unavailable")

    # ---------- 单曲索引 ----------

    def _start_track_index(self):
        """启动一次后台建库；已有索引则直接返回。"""
        with Spider._index_lock:
            if Spider._index_started:
                return
            Spider._index_started = True
        threading.Thread(target=self._build_track_index, daemon=True).start()

    def _build_track_index(self):
        """只建在内存里，不做任何磁盘写入。"""
        try:
            with Spider._index_lock:
                Spider._index_tracks = []
                Spider._index_strings = {}
                Spider._index_deep_page = 1
            # 热歌最稳，先建；再补两页歌单（经典老歌多）；然后榜单；最后继续扩歌单
            self._index_section("hot")
            self._index_deep(2)
            self._index_section("ranking")
            Spider._index_ready.set()
            self._index_deep()
        except Exception:
            pass
        finally:
            Spider._index_ready.set()

    def _index_section(self, section):
        albums = self._all_albums(section)
        if albums:
            self._index_albums(albums)

    def _index_deep(self, pages=None):
        """歌单分区只扩前 40 页：全库 1200 万首，纯内存装不下。"""
        albums, seen = [], set()
        stop = INDEX_DEEP_PAGES
        if pages is not None:
            stop = min(stop, Spider._index_deep_page + pages - 1)
        while Spider._index_deep_page <= stop:
            page = Spider._index_deep_page
            try:
                data = self._music_albums(INDEX_DEEP_SECTION, page, "",
                                          page_size=LIST_PAGE_SIZE) or {}
            except Exception:
                break
            batch = data.get("items") or []
            for item in batch:
                album_id = (item.get("id") or item.get("album_id")
                            or item.get("albumId"))
                if album_id and album_id not in seen:
                    seen.add(album_id)
                    albums.append((str(album_id), item))
            Spider._index_deep_page = page + 1
            if not data.get("has_more"):
                break
        if albums:
            self._index_albums(albums, limit=INDEX_DEEP_TRACK_LIMIT)

    def _all_albums(self, section):
        albums, seen = [], set()
        for page in range(1, 4):
            try:
                data = self._music_albums(section, page, "",
                                          page_size=INDEX_PAGE_SIZE) or {}
            except Exception:
                break
            batch = data.get("items") or []
            for item in batch:
                album_id = (item.get("id") or item.get("album_id")
                            or item.get("albumId"))
                if album_id and album_id not in seen:
                    seen.add(album_id)
                    albums.append((str(album_id), item))
            if not data.get("has_more") or not batch:
                break
        return albums

    def _album_chapters(self, album_id):
        for attempt in range(3):
            try:
                result = self._call("music.tracks",
                                    {"album_id": album_id}) or {}
                if self._to_int(result.get("code"), 0) == 200:
                    data = result.get("data") or {}
                    return data.get("chapters") or []
            except Exception:
                pass
            time.sleep(0.3 + attempt * 0.6)
        return []

    @staticmethod
    def _index_intern(value):
        """索引里的字符串大量重复，驻留后可省一半以上内存。"""
        if not value:
            return ""
        cached = Spider._index_strings.get(value)
        if cached is not None:
            return cached
        Spider._index_strings[value] = value
        return value

    def _index_size(self):
        return len(Spider._index_tracks)

    def _index_append(self, entries):
        if not entries:
            return
        with Spider._index_lock:
            Spider._index_tracks.extend(entries)

    def _index_albums(self, albums, limit=None):
        if limit and self._index_size() >= limit:
            return
        chunks = [albums[i::INDEX_WORKERS] for i in range(INDEX_WORKERS)]

        def worker(chunk):
            for album_id, item in chunk:
                if limit and self._index_size() >= limit:
                    return
                album_name = self._clean(item.get("title"))
                entries = []
                for track in self._album_chapters(album_id):
                    title = self._clean(track.get("title"))
                    index = self._to_int(track.get("index"), 0)
                    if not title or index <= 0:
                        continue
                    entries.append((Spider._index_intern(title),
                                    Spider._index_intern(
                                        self._clean(track.get("artist"))),
                                    Spider._index_intern(
                                        self._clean(track.get("album"))
                                        or album_name),
                                    album_id, index))
                self._index_append(entries)

        threads = [threading.Thread(target=worker, args=(chunk,), daemon=True)
                   for chunk in chunks]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()

    def _wait_index(self, timeout):
        if Spider._index_ready.is_set() or Spider._index_tracks:
            return
        Spider._index_ready.wait(timeout)

    @staticmethod
    def _match_score(keyword, title, artist, album):
        kw = (keyword or "").lower()
        if not kw:
            return None
        t = (title or "").lower()
        a = (artist or "").lower()
        al = (album or "").lower()
        if t == kw:
            return 0.0
        if t.startswith(kw):
            return 1.0
        pos = t.find(kw)
        if pos >= 0:
            # 关键词越靠前越相关，避免「周杰伦 - 稻香」排在大量歌名前
            return 2.0 + min(pos, 90) / 100.0
        if a == kw:
            return 3.0
        pos = a.find(kw)
        if pos >= 0:
            return 4.0 + min(pos, 90) / 100.0
        if kw in al:
            return 5.0
        return None

    @staticmethod
    def _fuzzy_score(keyword, title):
        """关键词按顺序出现在标题里（如漏了「过」）时的兜底分。"""
        kw = (keyword or "").lower()
        t = (title or "").lower()
        if len(kw) < 4 or len(t) <= len(kw):
            return None
        if len(kw) * 10 < len(t) * 6:
            return None
        pos, last, gaps = 0, -1, 0
        for ch in kw:
            hit = t.find(ch, pos)
            if hit < 0:
                return None
            if last >= 0:
                gaps += hit - last - 1
            last = hit
            pos = hit + 1
        if gaps > max(2, len(kw) // 2):
            return None
        return 4.8 + gaps * 0.05

    def _index_search(self, keyword, tokens=None):
        with Spider._index_lock:
            snapshot = list(Spider._index_tracks)
        if not snapshot:
            return []
        tokens = [token for token in (tokens or [])
                  if token and token != keyword]
        scored = []
        for title, artist, album, album_id, index in snapshot:
            full = self._match_score(keyword, title, artist, album)
            token_scores = [self._match_score(token, title, artist, album)
                            for token in tokens]
            matched_tokens = [s for s in token_scores if s is not None]
            if full is not None:
                best = full
            elif tokens and len(matched_tokens) == len(tokens):
                # 多个关键词同时命中（如「周杰伦 稻香」），优先于只命中一个词的
                best = 0.5 + min(matched_tokens) / 100.0
            elif matched_tokens:
                best = min(matched_tokens) + 2.0
            else:
                continue
            scored.append((best, len(title), title, artist, album,
                           album_id, index))
        # 精确/包含都没命中足够结果时，再按「顺序包含」兜底一次，
        # 解决「雨后的风景」找不到「雨过后的风景」这类漏字。
        if (len(scored) < INDEX_SCAN_MIN and len(keyword) >= 4
                and not re.search(r"\s", keyword)):
            found = {(row[5], row[6]) for row in scored}
            for title, artist, album, album_id, index in snapshot:
                if (album_id, index) in found:
                    continue
                score = self._fuzzy_score(keyword, title)
                if score is None:
                    continue
                scored.append((score, len(title), title, artist, album,
                               album_id, index))
        scored.sort(key=lambda row: (row[0], row[1]))
        return [self._track_to_vod(row[2], row[3], row[4], row[5], row[6])
                for row in scored[:200]]

    def _scan_album_tracks(self, hits, keyword, budget=8, wait=5):
        """对接口命中的专辑反查曲目：歌手名/歌单名命中时，这里能捞出单曲。"""
        ordered = ([hit for hit in hits if hit[0] in ("artist", "playlist")]
                   + [hit for hit in hits if hit[0] not in ("artist", "playlist")])
        selected, seen = [], set()
        for section, item in ordered:
            album_id = (item.get("id") or item.get("album_id")
                        or item.get("albumId"))
            if not album_id or album_id in seen:
                continue
            seen.add(album_id)
            selected.append((str(album_id), self._clean(item.get("title"))))
            if len(selected) >= budget:
                break
        if not selected:
            return []

        found, fresh, lock = [], [], threading.Lock()

        def worker(chunk):
            for album_id, album_title in chunk:
                for track in self._album_chapters(album_id):
                    title = self._clean(track.get("title"))
                    artist = self._clean(track.get("artist"))
                    album = self._clean(track.get("album")) or album_title
                    score = self._match_score(keyword, title, artist, album)
                    if score is None:
                        score = self._fuzzy_score(keyword, title)
                    index = self._to_int(track.get("index"), 0)
                    # 只认歌名/歌手命中；只有专辑名命中的会带来大量无关曲目
                    if score is None or score >= 5 or not title or index <= 0:
                        continue
                    vod = self._track_to_vod(title, artist, album,
                                             album_id, index)
                    entry = (Spider._index_intern(title),
                             Spider._index_intern(artist),
                             Spider._index_intern(album), album_id, index)
                    with lock:
                        fresh.append(entry)
                        found.append((score, len(title), vod))

        chunks = [selected[i::INDEX_SCAN_WORKERS]
                  for i in range(INDEX_SCAN_WORKERS)]
        threads = [threading.Thread(target=worker, args=(chunk,), daemon=True)
                   for chunk in chunks]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(wait)
        # 反查过的曲目顺手并入曲库，下次同样关键词直接命中
        if len(self._index_tracks) < INDEX_DEEP_TRACK_LIMIT:
            self._index_append(fresh)
        found.sort(key=lambda row: (row[0], row[1]))
        return [row[2] for row in found[:200]]

    @staticmethod
    def _track_to_vod(title, artist, album, album_id, index):
        title = Spider._clean(title)
        artist = Spider._clean(artist)
        name = title or ("第%d首" % index)
        if artist and artist not in name:
            name += " - " + artist
        remarks = INDEX_SOURCE_TAG
        if album:
            remarks += " · " + album
        return {
            "vod_id": "track:%s:%d" % (album_id, index),
            "vod_name": name,
            "vod_pic": DEFAULT_COVER,
            "vod_actor": artist,
            "vod_remarks": Spider._clean(remarks),
        }

    @staticmethod
    def _dedupe_tracks(tracks):
        merged, seen = [], set()
        for vod in tracks:
            key = (vod.get("vod_name") or "").lower()
            if not key or key in seen:
                continue
            seen.add(key)
            merged.append(vod)
        return merged

    @staticmethod
    def _dedupe_vods(vods):
        merged, seen = [], set()
        for vod in vods:
            vid = vod.get("vod_id")
            if not vid or vid in seen:
                continue
            seen.add(vid)
            merged.append(vod)
        return merged

    def _track_detail(self, vid):
        match = re.match(r"^track:([0-9A-Za-z-]+):(\d+)$", vid)
        if not match:
            return {"list": []}
        album_id, want = match.group(1), int(match.group(2))

        album = {}
        try:
            result = self._call("music.album", {"album_id": album_id}) or {}
            if isinstance(result.get("data"), dict):
                album = result["data"]
        except Exception:
            album = {}

        track = {}
        for item in self._album_chapters(album_id):
            if self._to_int(item.get("index"), 0) == want:
                track = item
                break
        if not track:
            return {"list": []}

        title = self._clean(track.get("title")) or ("第%d首" % want)
        artist = self._clean(track.get("artist"))
        album_title = (self._clean(track.get("album"))
                       or self._clean(album.get("title")))
        duration = self._to_int(track.get("duration"), 0)

        label = title
        if artist and artist not in label:
            label += " - " + artist
        label = "%02d. %s" % (want, label)

        notes = []
        if artist:
            notes.append("歌手：" + artist)
        if album_title:
            notes.append("专辑：" + album_title)
        if duration:
            notes.append("时长：%d:%02d" % (duration // 60, duration % 60))
        notes.append("单曲播放。")

        vod = {
            "vod_id": vid,
            "vod_name": title + (" - " + artist if artist and artist not in title else ""),
            "vod_pic": self._img(album.get("cover_url") or DEFAULT_COVER),
            "vod_actor": artist,
            "vod_content": "\n".join(notes),
            "vod_remarks": INDEX_SOURCE_TAG,
            "vod_play_from": "听友音乐",
            "vod_play_url": "%s$play/%s/%d" % (label, album_id, want),
        }
        return {"list": [vod]}

    # ---------- 游客身份 ----------

    def _ensure_token(self):
        now = time.monotonic()
        with Spider._identity_lock:
            if Spider._token and now - Spider._token_time < TOKEN_TTL:
                self._token = Spider._token
                self._device_id = Spider._device_id
                return
            if not Spider._device_id:
                Spider._device_id = str(uuid.uuid4())
            self._device_id = Spider._device_id
            body_obj = {"content": ""}
            body_obj.update(self._identity())
            plain = json.dumps(body_obj, ensure_ascii=False, separators=(",", ":"))
            encrypted = _b64(self._cipher.encrypt(plain.encode("utf-8")))
            signature = _b64(hmac.new(SIGN_KEY, encrypted.encode("ascii"),
                                      hashlib.sha256).digest())
            headers = dict(BASE_HEADERS)
            headers["X-Post-Signature"] = signature
            headers["X-Device-Id"] = self._device_id

            result = None
            last_error = None
            for base in self._candidate_bases():
                try:
                    text = self._fetch_text(
                        base + "/web/user/register/temp", headers,
                        encrypted.encode("utf-8"))
                    if not text:
                        continue
                    data = json.loads(
                        self._cipher.decrypt(_unb64(text)).decode("utf-8"))
                    if not isinstance(data, dict):
                        continue
                    if ((data.get("data") or {}).get("tokens") or {}).get("accessToken"):
                        result = data
                        self._base = base
                        break
                    code = self._to_int(data.get("code"), 0)
                    if code == 429 or code >= 500:
                        result = data
                        continue
                    result = data
                    break
                except Exception as error:
                    last_error = error
            if not isinstance(result, dict):
                if last_error:
                    raise last_error
                raise RuntimeError("guest register failed")

            token = ((result.get("data") or {}).get("tokens") or {}).get("accessToken")
            if not token:
                raise RuntimeError(self._clean(result.get("message")) or "guest register failed")
            Spider._token = str(token)
            Spider._token_time = time.monotonic()
            self._token = Spider._token

    def _reset_identity(self):
        with Spider._identity_lock:
            Spider._token = ""
            Spider._token_time = 0.0
            Spider._device_id = str(uuid.uuid4())
            self._token = ""
            self._device_id = Spider._device_id

    def _identity(self):
        if not self._device_id:
            self._device_id = Spider._device_id or str(uuid.uuid4())
            Spider._device_id = self._device_id
        return {
            "device_id": self._device_id,
            "brand": "BROWSER",
            "model": "Chrome",
            "appVer": "124",
            "osVer": "1",
            "timestamp": int(time.time()),
        }

    # ---------- 网络 ----------

    def _candidate_bases(self):
        if self._base:
            return [self._base] + [b for b in API_BASES if b != self._base]
        self._base = API_BASES[0]
        return [self._base] + [b for b in API_BASES if b != self._base]

    def _fetch_text(self, url, headers, body):
        try:
            text = _pooled_post(url, headers, body)
        except Exception:
            text = ""
        if text:
            return text
        try:
            request = urllib.request.Request(
                url, data=body, headers=headers, method="POST")
            with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
                text = response.read().decode("utf-8", errors="ignore")
                if text:
                    return text
        except urllib.error.HTTPError as error:
            # 401/429/5xx 也可能带加密响应体，读出来交给上层判断
            try:
                text = error.read().decode("utf-8", errors="ignore")
                if text:
                    return text
            except Exception:
                pass
        except Exception:
            pass
        try:
            response = self.fetch(url, headers=headers, data=body)
            text = self._response_text(response)
            if text:
                return text
        except TypeError:
            pass
        except Exception:
            pass
        return ""

    @staticmethod
    def _response_text(response):
        if response is None:
            return ""
        if isinstance(response, bytes):
            return response.decode("utf-8", errors="ignore")
        if isinstance(response, str):
            return response
        text = getattr(response, "text", None)
        if text:
            return str(text)
        content = getattr(response, "content", None)
        if content:
            return bytes(content).decode("utf-8", errors="ignore")
        return ""

    # ---------- 数据转换 ----------

    def _album_to_vod(self, item):
        album_id = (item.get("id") or item.get("album_id")
                    or item.get("albumId"))
        if not album_id:
            return None
        bits = []
        count = self._to_int(item.get("count"), 0)
        if count:
            bits.append("%d首" % count)
        cat = self._clean(item.get("cat"))
        if cat:
            bits.append(cat)
        author = self._clean(item.get("author") or item.get("teller"))
        if author and author != "合集" and author != cat:
            bits.append(author)

        return {
            "vod_id": "music:" + str(album_id),
            "vod_name": (self._clean(item.get("title") or item.get("name"))
                         or "未知专辑"),
            "vod_pic": self._img(item.get("cover_url") or DEFAULT_COVER),
            "vod_actor": author,
            "vod_remarks": " · ".join(bits),
        }

    # ---------- 工具 ----------

    @staticmethod
    def _album_id(vid):
        value = str(vid or "").strip()
        if value.startswith("music:"):
            value = value[6:]
        match = re.search(
            r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-"
            r"[0-9a-fA-F]{4}-[0-9a-fA-F]{12}", value)
        if match:
            return match.group(0)
        return value if re.match(r"^[0-9A-Za-z-]{6,64}$", value) else ""

    @staticmethod
    def _as_dict(value):
        if isinstance(value, dict):
            return value
        if isinstance(value, str) and value.strip().startswith("{"):
            try:
                data = json.loads(value)
                return data if isinstance(data, dict) else {}
            except ValueError:
                return {}
        return {}

    @staticmethod
    def _to_int(value, default=0):
        try:
            return int(value)
        except (TypeError, ValueError):
            return default

    @staticmethod
    def _pagecount(total, size, page, has_more):
        if total > 0 and size > 0:
            return max(1, (total + size - 1) // size)
        return max(1, page + 1 if has_more else page)

    @staticmethod
    def _clean(text):
        if not text:
            return ""
        value = html.unescape(str(text))
        value = re.sub(r"<[^>]+>", "", value)
        value = value.replace("$", " ").replace("#", " ")
        value = re.sub(r"\s+", " ", value)
        return value.strip()

    @staticmethod
    def _img(path):
        value = (path or "").strip()
        if not value:
            return ""
        if value.startswith("//"):
            value = "https:" + value
        elif value.startswith("http://"):
            value = "https://" + value[7:]
        return value
