# -*- coding: utf-8 -*-
"""
番茄TV —— 番茄系内容聚合（ch6vip/fqapp 上游链路）TVBox/OK影视 点播源
覆盖五类：小说 / 短剧 / 漫画 / 漫剧 / 听书

  * 上游为字节番茄系 API，请求需字节 v2 签名（x-khronos / x-ladon /
    x-argus 等），纯 Python 复刻并与 fqapp 金向量对齐；设备自动注册带缓存。
  * 视频/听书为 CENC(AES-CTR) 加密 mp4/m4a，由内置本地代理流式解密
    供播放器拉取；小说正文走 novel:// 协议。
  * 短剧/漫剧详情提供 1080P~360P 五档清晰度多线路（红果式 $$$ 分组），
    按档位名选流、缺失回退最高档。
  * 漫画图片 AES-256-GCM 经同代理 /img 解密，整话后台预加载 + 两级缓存。
  * 分页：短剧/漫剧只认 crt=1 且并发互踩游标，视频类走「串行 walk 缓冲」
    顺序拉取去重累积，对壳统一 20 条/页；深翻页同步补拉限 15s 预算，
    超时先出短页后台补足；短剧枯竭自动切 selector 内容源扩展深度。
    书籍三类 crt=2 步长 20 直取；首页五类并发 + 3 分钟缓存。

接口：homeContent / categoryContent / detailContent / searchContent /
playerContent。单文件、零第三方依赖。
"""

# -*- coding: utf-8 -*-
"""
fqbox —— 把开源项目 ch6vip/fqapp（番茄系内容聚合 App）的上游链路移植成的
TVBox/OK影视 点播源。覆盖：短剧 / 小说 / 漫画 / 漫剧 / 听书。

原理（源自对 com.dragon.read 即"番茄"上游的逆向，参考 ch6vip/fqapp 源码）：
  * 上游 = 字节番茄系 API（fqnovel.com / fanqiesdk.com），请求需字节 v2 签名：
      x-khronos / x-ss-req-ticket / x-ladon / x-argus / x-ss-stub(MD5)
  * 本文件用纯 Python 复刻这些签名原语（SM3 / Simon / ProtoBuf / Ladon / Argus），
    并与 fqapp 的 rust/testdata/vectors.json 金向量逐字节对齐。
  * 视频/短剧直链为 spade 密文，用 key_seed 经 SHA512+AES-CBC 解出。
  * 小说正文、漫画图片等亦有其解密契约，见对应函数。

单文件、零第三方依赖（AES-128 自实现，MD5/SHA 用标准库）。
"""

import base64
import hashlib
import html as _html_mod
import re as _re
import struct

MASK64 = (1 << 64) - 1
MASK32 = 0xFFFFFFFF


# ===========================================================================
# 纯 Python AES-128（ECB 单块 + CBC 模式），零依赖
# ===========================================================================
_AES_SBOX = bytes.fromhex(
    "637c777bf26b6fc53001672bfed7ab76ca82c97dfa5947f0add4a2af9ca472c0"
    "b7fd9326363ff7cc34a5e5f171d8311504c723c31896059a071280e2eb27b275"
    "09832c1a1b6e5aa0523bd6b329e32f8453d100ed20fcb15b6acbbe394a4c58cf"
    "d0efaafb434d338545f9027f503c9fa851a3408f929d38f5bcb6da2110fff3d2"
    "cd0c13ec5f974417c4a77e3d645d197360814fdc222a908846eeb814de5e0bdb"
    "e0323a0a4906245cc2d3ac629195e479e7c8376d8dd54ea96c56f4ea657aae08"
    "ba78252e1ca6b4c6e8dd741f4bbd8b8a703eb5664803f60e613557b986c11d9e"
    "e1f8981169d98e949b1e87e9ce5528df8ca1890dbfe6426841992d0fb054bb16")

_AES_INV_SBOX = [0] * 256
for _i, _v in enumerate(_AES_SBOX):
    _AES_INV_SBOX[_v] = _i
_AES_INV_SBOX = bytes(_AES_INV_SBOX)

_AES_RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]


def _aes_xtime(a):
    a <<= 1
    if a & 0x100:
        a = (a ^ 0x1b) & 0xff
    return a


def _aes_mul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        b >>= 1
        a = _aes_xtime(a)
    return p & 0xff


def _aes_expand(key16):
    # 11 组轮密钥，每组 16 字节
    w = [list(key16[i * 4:i * 4 + 4]) for i in range(4)]
    for i in range(4, 44):
        t = list(w[i - 1])
        if i % 4 == 0:
            t = t[1:] + t[:1]
            t = [_AES_SBOX[b] for b in t]
            t[0] ^= _AES_RCON[i // 4 - 1]
        w.append([w[i - 4][j] ^ t[j] for j in range(4)])
    rk = []
    for r in range(11):
        rk.append(bytes(b for word in w[r * 4:r * 4 + 4] for b in word))
    return rk


def _aes_encrypt_block(block, rk):
    s = [block[i] ^ rk[0][i] for i in range(16)]

    def add_round_key(state, r):
        return [state[i] ^ r[i] for i in range(16)]

    def sub_shift(state):
        out = [0] * 16
        for c in range(4):
            for r in range(4):
                out[c * 4 + r] = _AES_SBOX[state[((c + r) % 4) * 4 + r]]
        return out

    def mix(state):
        out = [0] * 16
        for c in range(4):
            col = state[c * 4:c * 4 + 4]
            out[c * 4 + 0] = _aes_mul(col[0], 2) ^ _aes_mul(col[1], 3) ^ col[2] ^ col[3]
            out[c * 4 + 1] = col[0] ^ _aes_mul(col[1], 2) ^ _aes_mul(col[2], 3) ^ col[3]
            out[c * 4 + 2] = col[0] ^ col[1] ^ _aes_mul(col[2], 2) ^ _aes_mul(col[3], 3)
            out[c * 4 + 3] = _aes_mul(col[0], 3) ^ col[1] ^ col[2] ^ _aes_mul(col[3], 2)
        return out

    for rnd in range(1, 10):
        s = sub_shift(s)
        s = mix(s)
        s = add_round_key(s, rk[rnd])
    s = sub_shift(s)
    s = add_round_key(s, rk[10])
    return bytes(s)


def _aes_decrypt_block(block, rk):
    def add_round_key(state, r):
        return [state[i] ^ r[i] for i in range(16)]

    def inv_sub_shift(state):
        out = [0] * 16
        for c in range(4):
            for r in range(4):
                out[((c + r) % 4) * 4 + r] = _AES_INV_SBOX[state[c * 4 + r]]
        return out

    def inv_mix(state):
        out = [0] * 16
        for c in range(4):
            col = state[c * 4:c * 4 + 4]
            out[c * 4 + 0] = _aes_mul(col[0], 14) ^ _aes_mul(col[1], 11) ^ _aes_mul(col[2], 13) ^ _aes_mul(col[3], 9)
            out[c * 4 + 1] = _aes_mul(col[0], 9) ^ _aes_mul(col[1], 14) ^ _aes_mul(col[2], 11) ^ _aes_mul(col[3], 13)
            out[c * 4 + 2] = _aes_mul(col[0], 13) ^ _aes_mul(col[1], 9) ^ _aes_mul(col[2], 14) ^ _aes_mul(col[3], 11)
            out[c * 4 + 3] = _aes_mul(col[0], 11) ^ _aes_mul(col[1], 13) ^ _aes_mul(col[2], 9) ^ _aes_mul(col[3], 14)
        return out

    s = add_round_key(list(block), rk[10])
    s = inv_sub_shift(s)
    for rnd in range(9, 0, -1):
        s = add_round_key(s, rk[rnd])
        s = inv_mix(s)
        s = inv_sub_shift(s)
    s = add_round_key(s, rk[0])
    return bytes(s)


def aes_cbc_encrypt(data, key, iv):
    assert len(key) in (16, 32) and len(data) % 16 == 0
    rk = _aes_expand(key)
    prev = iv
    out = bytearray()
    for i in range(0, len(data), 16):
        blk = bytes(a ^ b for a, b in zip(data[i:i + 16], prev))
        enc = _aes_encrypt_block(blk, rk)
        out.extend(enc)
        prev = enc
    return bytes(out)


def aes_cbc_decrypt(data, key, iv):
    assert len(key) in (16, 32) and len(data) % 16 == 0
    rk = _aes_expand(key)
    prev = iv
    out = bytearray()
    for i in range(0, len(data), 16):
        blk = data[i:i + 16]
        dec = _aes_decrypt_block(blk, rk)
        out.extend(bytes(a ^ b for a, b in zip(dec, prev)))
        prev = blk
    return bytes(out)


def pkcs7_pad(data, block=16):
    pad = block - (len(data) % block)
    return data + bytes([pad]) * pad


def pkcs7_unpad(data, block=16):
    if not data:
        return data
    pad = data[-1]
    if 0 < pad <= block and pad <= len(data):
        return data[:-pad]
    return data


# ===========================================================================
# SM3 国密哈希（翻译自 sign/sm3.rs）
# ===========================================================================
_SM3_IV = [0x7380166f, 0x4914b2b9, 0x172442d7, 0xda8a0600,
           0xa96f30bc, 0x163138aa, 0xe38dee4d, 0xb0fb0e4e]


def _sm3_rotl(a, k):
    k %= 32
    if k == 0:
        return a & MASK32
    return ((a << k) | (a >> (32 - k))) & MASK32


def _sm3_ff(x, y, z, j):
    return (x ^ y ^ z) if j < 16 else ((x & y) | (x & z) | (y & z))


def _sm3_gg(x, y, z, j):
    return (x ^ y ^ z) if j < 16 else ((x & y) | ((~x) & z))


def _sm3_p0(x):
    return (x ^ _sm3_rotl(x, 9) ^ _sm3_rotl(x, 17)) & MASK32


def _sm3_p1(x):
    return (x ^ _sm3_rotl(x, 15) ^ _sm3_rotl(x, 23)) & MASK32


def _sm3_cf(v, block):
    w = [0] * 68
    for i in range(16):
        w[i] = struct.unpack(">I", block[i * 4:i * 4 + 4])[0]
    for j in range(16, 68):
        w[j] = (_sm3_p1(w[j - 16] ^ w[j - 9] ^ _sm3_rotl(w[j - 3], 15))
                ^ _sm3_rotl(w[j - 13], 7) ^ w[j - 6]) & MASK32
    w1 = [w[j] ^ w[j + 4] for j in range(64)]
    a, b, c, d, e, f, g, h = v
    for j in range(64):
        tj = 0x79cc4519 if j < 16 else 0x7a879d8a
        ss1 = _sm3_rotl((_sm3_rotl(a, 12) + e + _sm3_rotl(tj, j)) & MASK32, 7)
        ss2 = ss1 ^ _sm3_rotl(a, 12)
        tt1 = (_sm3_ff(a, b, c, j) + d + ss2 + w1[j]) & MASK32
        tt2 = (_sm3_gg(e, f, g, j) + h + ss1 + w[j]) & MASK32
        d = c
        c = _sm3_rotl(b, 9)
        b = a
        a = tt1
        h = g
        g = _sm3_rotl(f, 19)
        f = e
        e = _sm3_p0(tt2)
    return [(a ^ v[0]) & MASK32, (b ^ v[1]) & MASK32, (c ^ v[2]) & MASK32, (d ^ v[3]) & MASK32,
            (e ^ v[4]) & MASK32, (f ^ v[5]) & MASK32, (g ^ v[6]) & MASK32, (h ^ v[7]) & MASK32]


def sm3_hash(msg):
    orig = len(msg)
    padded = bytearray(msg)
    padded.append(0x80)
    reserve = (orig % 64) + 1
    range_end = 56
    if range_end < reserve:
        range_end += 64
    padded.extend(b"\x00" * (range_end - reserve))
    padded.extend(struct.pack(">Q", (orig * 8) & MASK64))
    v = list(_SM3_IV)
    for i in range(len(padded) // 64):
        v = _sm3_cf(v, bytes(padded[i * 64:i * 64 + 64]))
    out = bytearray()
    for x in v:
        out.extend(struct.pack(">I", x))
    return bytes(out)


# ===========================================================================
# Simon 分组密码（128-bit key, 64-bit block, 72 rounds，翻译自 sign/simon.rs）
# ===========================================================================
_SIMON_Z = 0x3DC94C3A046D678B


def _rotl64(v, n):
    n &= 63
    return ((v << n) | (v >> (64 - n))) & MASK64 if n else v & MASK64


def _rotr64(v, n):
    n &= 63
    return ((v >> n) | (v << (64 - n))) & MASK64 if n else v & MASK64


def _simon_key_expansion(key4):
    k = [key4[0], key4[1], key4[2], key4[3]] + [0] * 68
    for i in range(4, 72):
        tmp = _rotr64(k[i - 1], 3) ^ k[i - 3]
        tmp ^= _rotr64(tmp, 1)
        not_val = (~k[i - 4]) & MASK64
        bit_val = (_SIMON_Z >> ((i - 4) % 62)) & 1
        k[i] = (not_val ^ tmp ^ bit_val ^ 3) & MASK64
    return k


def simon_enc(pt, key4):
    k = _simon_key_expansion(key4)
    xi, xi1 = pt[0] & MASK64, pt[1] & MASK64
    for rk in k:
        tmp = xi1
        f = _rotl64(xi1, 1) & _rotl64(xi1, 8)
        xi1 = (xi ^ f ^ _rotl64(xi1, 2) ^ rk) & MASK64
        xi = tmp
    return [xi, xi1]


# ===========================================================================
# ProtoBuf 编码器（翻译自 sign/protobuf.rs，write_varint 掩码到 32 位）
# ===========================================================================
class ProtoBuf:
    def __init__(self):
        self.fields = []   # (idx, typ, v_uint, blob_index)
        self.blobs = []

    def put_varint(self, idx, v):
        self.fields.append((idx, 0, v & MASK64, 0))

    def _put_blob(self, idx, data):
        self.blobs.append(bytes(data))
        self.fields.append((idx, 2, 0, len(self.blobs) - 1))

    def put_utf8(self, idx, s):
        self._put_blob(idx, s.encode("utf-8"))

    def put_bytes(self, idx, data):
        self._put_blob(idx, data)

    def put_protobuf(self, idx, nested):
        self._put_blob(idx, nested.to_buf())

    def to_buf(self):
        out = bytearray()
        for idx, typ, v_uint, bidx in self.fields:
            key = ((idx << 3) | (typ & 7)) & MASK64
            _write_varint(out, key)
            if typ == 5:
                out.extend(struct.pack("<I", v_uint & MASK32))
            elif typ == 1:
                out.extend(struct.pack("<Q", v_uint & MASK64))
            elif typ == 0:
                _write_varint(out, v_uint)
            elif typ == 2:
                blob = self.blobs[bidx]
                _write_varint(out, len(blob) & MASK64)
                out.extend(blob)
        return bytes(out)


def _write_varint(dst, v):
    v &= 0xFFFFFFFF
    while v >= 128:
        dst.append(((v & 127) | 128) & 0xff)
        v >>= 7
    dst.append(v & 0x7f)


# ===========================================================================
# X-Ladon（翻译自 sign/ladon.rs）：34 轮 ARX 分组密码 + MD5 密钥派生
# ===========================================================================
def ladon_expand_hash_table(md5_hex):
    ht = bytearray(288)
    mb = md5_hex.encode("utf-8")[:32]
    ht[:len(mb)] = mb

    def load(off):
        v = 0
        for j in range(8):
            v |= ht[off + j] << (j * 8)
        return v

    temp = [load(0), load(8), load(16), load(24)]
    buf_b0, buf_b8 = temp[0], temp[1]
    temp = temp[2:]
    for i in range(34):
        x9 = buf_b0
        x8 = _rotr64(buf_b8, 8)
        x8 = (x8 + x9) & MASK64
        x8 ^= i
        temp.append(x8)
        x8 ^= _rotl64(x9, 3)
        for j in range(8):
            ht[(i + 1) * 8 + j] = (x8 >> (j * 8)) & 255
        buf_b0 = x8
        buf_b8 = temp[0]
        temp.pop(0)
    return bytes(ht)


def ladon_encrypt_block(ht, block):
    data0 = 0
    data1 = 0
    for i in range(8):
        data0 |= block[i] << (i * 8)
        data1 |= block[8 + i] << (i * 8)
    for i in range(34):
        h = 0
        for j in range(8):
            h |= ht[i * 8 + j] << (j * 8)
        rotated = _rotr64(data1, 8)
        s = (data0 + rotated) & MASK64
        data1 = h ^ s
        rotated = _rotl64(data0, 3)
        data0 = data1 ^ rotated
    out = bytearray(16)
    for i in range(8):
        out[i] = (data0 >> (i * 8)) & 255
        out[8 + i] = (data1 >> (i * 8)) & 255
    return bytes(out)


def ladon_encrypt_raw(md5_hex, data):
    ht = ladon_expand_hash_table(md5_hex)
    size = len(data)
    pad_val = 16 - (size % 16)
    new_size = size + pad_val
    inp = bytes(data) + bytes([pad_val]) * pad_val
    out = bytearray()
    for i in range(new_size // 16):
        out.extend(ladon_encrypt_block(ht, inp[i * 16:i * 16 + 16]))
    return bytes(out)


def ladon_encrypt(khronos, lc_id, aid, random_bytes):
    data = "%d-%d-%d" % (khronos, lc_id, aid)
    keygen = bytes(random_bytes) + str(aid).encode("utf-8")
    md5_hex = hashlib.md5(keygen).hexdigest()
    enc = ladon_encrypt_raw(md5_hex, data.encode("utf-8"))
    return base64.b64encode(bytes(random_bytes) + enc).decode("ascii")


# ===========================================================================
# X-Argus（翻译自 sign/argus.rs）：ProtoBuf bean -> PKCS7 -> Simon -> AES-CBC
# ===========================================================================
_ARGUS_SIGN_KEY = bytes.fromhex("fc78e0a9657a0c748ce51559903ccf03510e51d3cff232d71343e88a321c5304")
_ARGUS_AES_KEY = bytes.fromhex("d31e3718288a1027baab59f146a09a9c")
_ARGUS_AES_IV = bytes.fromhex("ea180a0336ed352fcd24e4d50018ae54")
_ARGUS_MAGIC8 = bytes([0xf2, 0xf7, 0xfc, 0xff, 0xf2, 0xf7, 0xfc, 0xff])
_ARGUS_TAIL9 = bytes([0xea, 0xfb, 0x2c, 0xfe, 0x85, 0x68, 0x51, 0x91, 0x54])
_ARGUS_PREFIX = bytes([0xf2, 0x81])


def _sm3_prefix6(msg):
    return sm3_hash(msg)[:6]


def argus_body_hash(stub_hex):
    if not stub_hex:
        return _sm3_prefix6(bytes(16))
    return _sm3_prefix6(bytes.fromhex(stub_hex))


def argus_query_hash(query):
    if not query:
        return _sm3_prefix6(bytes(16))
    return _sm3_prefix6(query.encode("utf-8"))


def argus_encrypt_enc_pb(data, length):
    buf = bytearray(length)
    n = min(len(data), length)
    buf[:n] = data[:n]
    xk = data[:8]
    for i in range(8, length):
        src = data[i] if i < len(data) else 0
        buf[i] = src ^ xk[i % 8]
    buf.reverse()
    return bytes(buf)


def _simon_key_list():
    key = _ARGUS_SIGN_KEY
    return [struct.unpack("<Q", key[i * 8:i * 8 + 8])[0] for i in range(4)]


def _simon_encrypt_padded(protobuf):
    key = _simon_key_list()
    enc = bytearray(len(protobuf))
    for i in range(len(protobuf) // 16):
        blk = protobuf[i * 16:i * 16 + 16]
        a = struct.unpack("<Q", blk[:8])[0]
        b = struct.unpack("<Q", blk[8:])[0]
        ct = simon_enc([a, b], key)
        enc[i * 16:i * 16 + 8] = struct.pack("<Q", ct[0])
        enc[i * 16 + 8:i * 16 + 16] = struct.pack("<Q", ct[1])
    return bytes(enc)


def _pkcs7_align(data):
    pad = 16 - (len(data) % 16)
    return bytes(data) + bytes([pad]) * pad


def argus_encrypt(bean):
    protobuf = _pkcs7_align(bean.to_buf())
    new_len = len(protobuf)
    enc_pb = _simon_encrypt_padded(protobuf)
    b_buffer = bytearray(argus_encrypt_enc_pb(enc_pb, new_len + 8))
    b_buffer += b"ao"
    b_buffer = bytearray(_pkcs7_align(bytes(b_buffer)))
    out = aes_cbc_encrypt(bytes(b_buffer), _ARGUS_AES_KEY, _ARGUS_AES_IV)
    return base64.b64encode(out).decode("ascii")


def argus_encrypt_551(bean):
    protobuf = _pkcs7_align(bean.to_buf())
    enc_pb = _simon_encrypt_padded(protobuf)
    un = bytes(_ARGUS_MAGIC8) + enc_pb + bytes(_ARGUS_TAIL9)
    buf = bytearray(len(un))
    buf[:8] = _ARGUS_MAGIC8
    for i in range(8, len(un)):
        buf[i] = un[i] ^ _ARGUS_MAGIC8[i % 8]
    buf.reverse()
    buf += b"ao"
    buf = bytearray(_pkcs7_align(bytes(buf)))
    out = aes_cbc_encrypt(bytes(buf), _ARGUS_AES_KEY, _ARGUS_AES_IV)
    raw = bytes(_ARGUS_PREFIX) + out
    return base64.b64encode(raw).decode("ascii")


def argus_get_sign(query_string, stub_hex, timestamp, aid, license_id,
                   device_id, install_id, rand_field, style551=True):
    if aid == 0:
        aid = 1967
    if license_id == 0:
        license_id = 1611921764
    bean = ProtoBuf()
    bean.put_varint(1, 1077940818)
    bean.put_varint(2, 2)
    bean.put_varint(3, rand_field)
    bean.put_utf8(4, str(aid))
    bean.put_utf8(5, device_id)
    bean.put_utf8(6, str(license_id))
    bean.put_utf8(7, _query_param(query_string, "version_name") or "")
    if style551:
        bean.put_utf8(8, "v04.04.05-ov-android")
        bean.put_varint(9, 134744640)
        bean.put_bytes(10, bytes(8))
        bean.put_varint(11, 0)
    else:
        bean.put_utf8(8, "")
        bean.put_varint(9, 0)
        bean.put_utf8(10, "")
        bean.put_utf8(11, "")
    bean.put_varint(12, (timestamp << 1) & MASK64)
    bean.put_bytes(13, argus_body_hash(stub_hex))
    bean.put_bytes(14, argus_query_hash(query_string))
    sub15 = ProtoBuf()
    sub15.put_varint(1, 1)
    sub15.put_varint(2, 1)
    sub15.put_varint(3, 1)
    sub15.put_varint(7, 0xC792ECCC)
    bean.put_protobuf(15, sub15)
    bean.put_utf8(16, install_id)
    bean.put_utf8(20, "none")
    bean.put_varint(21, 738)
    sub23 = ProtoBuf()
    sub23.put_utf8(1, "NX551J")
    sub23.put_varint(2, 8196)
    sub23.put_varint(4, 0x80E0D800)
    bean.put_protobuf(23, sub23)
    bean.put_varint(25, 2)
    if style551:
        return argus_encrypt_551(bean)
    return argus_encrypt(bean)


def _query_param(query_string, name):
    from urllib.parse import parse_qs
    try:
        d = parse_qs(query_string, keep_blank_values=True)
        v = d.get(name)
        return v[0] if v else None
    except Exception:
        return None


# ===========================================================================
# 哈希 / 压缩 / 随机 辅助（注册与请求 stub 用）
# ===========================================================================
import os as _os
import sys as _sys
import time as _time
import json as _json
import zlib as _zlib
import random as _random
import uuid as _uuid_mod
import http.client as _httpclient
import urllib.parse as _urlparse
import threading as _threading_module

try:
    import gzip as _gzip_mod
except Exception:
    _gzip_mod = None

# ---- MD5（hashlib 优先，FIPS 环境退化为纯 Python 实现）----
_MD5_K = (
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a,
    0xa8304613, 0xfd469501, 0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
    0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821, 0xf61e2562, 0xc040b340,
    0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8,
    0x676f02d9, 0x8d2a4c8a, 0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
    0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70, 0x289b7ec6, 0xeaa127fa,
    0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92,
    0xffeff47d, 0x85845dd1, 0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
    0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
)
_MD5_S = (
    7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
)


def _md5_pure(msg):
    a0, b0, c0, d0 = 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476
    msg = bytearray(msg)
    bit_len = (8 * len(msg)) & 0xFFFFFFFFFFFFFFFF
    msg.append(0x80)
    while len(msg) % 64 != 56:
        msg.append(0)
    msg += bit_len.to_bytes(8, "little")

    def _rotl(x, c):
        return ((x << c) | (x >> (32 - c))) & 0xFFFFFFFF

    for off in range(0, len(msg), 64):
        chunk = msg[off:off + 64]
        m = [int.from_bytes(chunk[i * 4:i * 4 + 4], "little") for i in range(16)]
        a, b, c, d = a0, b0, c0, d0
        for i in range(64):
            if i < 16:
                f = (b & c) | (~b & d) & 0xFFFFFFFF
                g = i
            elif i < 32:
                f = (d & b) | (~d & c) & 0xFFFFFFFF
                g = (5 * i + 1) % 16
            elif i < 48:
                f = b ^ c ^ d
                g = (3 * i + 5) % 16
            else:
                f = c ^ (b | (~d & 0xFFFFFFFF))
                g = (7 * i) % 16
            f = (f + a + _MD5_K[i] + m[g]) & 0xFFFFFFFF
            a, d, c = d, c, b
            b = (b + _rotl(f, _MD5_S[i])) & 0xFFFFFFFF
        a0 = (a0 + a) & 0xFFFFFFFF
        b0 = (b0 + b) & 0xFFFFFFFF
        c0 = (c0 + c) & 0xFFFFFFFF
        d0 = (d0 + d) & 0xFFFFFFFF
    return (a0.to_bytes(4, "little") + b0.to_bytes(4, "little") +
            c0.to_bytes(4, "little") + d0.to_bytes(4, "little"))


def md5_digest(data):
    """MD5(bytes) -> bytes；hashlib 不可用时退化纯 Python。"""
    data = bytes(data)
    try:
        return hashlib.md5(data).digest()
    except Exception:
        return _md5_pure(data)


def md5_hex(data):
    return md5_digest(data).hex()


def sha512(data):
    return hashlib.sha512(bytes(data)).digest()


def gzip_compress(data):
    """gzip deflate（mtime=0，兼容 Go/Flate2 的 gzip 容器）。"""
    co = _zlib.compressobj(6, _zlib.DEFLATED, 31)
    return co.compress(bytes(data)) + co.flush()


def gunzip_bytes(data):
    try:
        return _zlib.decompress(bytes(data), 31)
    except Exception:
        pass
    if _gzip_mod is not None:
        try:
            return _gzip_mod.decompress(bytes(data))
        except Exception:
            pass
    return None


def maybe_gunzip(data, resp_headers):
    ce = ""
    for k, v in (resp_headers or []):
        if k.lower() == "content-encoding":
            ce = (v or "").lower()
            break
    if "gzip" in ce or bytes(data[:2]) == b"\x1f\x8b":
        out = gunzip_bytes(data)
        if out is not None:
            return out
    return bytes(data)


def now_secs():
    return int(_time.time())


def now_millis():
    return int(_time.time() * 1000)


def uuid_v4():
    return str(_uuid_mod.uuid4())


def random_hex_lower(n):
    return _os.urandom(n).hex()


def random_alnum(n):
    chars = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    rb = _os.urandom(n)
    return bytes(chars[b % len(chars)] for b in rb).decode("ascii")


def rand_mac():
    return ":".join("%02X" % b for b in _os.urandom(6))


# ---- Go 的 url.Values 编码（注册用，无占位符还原）----
def go_query_escape(s):
    out = []
    for b in s.encode("utf-8"):
        if (0x41 <= b <= 0x5A or 0x61 <= b <= 0x7A or 0x30 <= b <= 0x39
                or b in (0x2D, 0x5F, 0x2E, 0x7E)):
            out.append(chr(b))
        elif b == 0x20:
            out.append("+")
        else:
            out.append("%%%02X" % b)
    return "".join(out)


def sorted_query(params):
    """Go 的 url.Values.Encode()：按 key 排序、转义、& 连接。"""
    v = sorted(params, key=lambda kv: kv[0])
    return "&".join("%s=%s" % (go_query_escape(k), go_query_escape(val)) for k, val in v)


def restore_placeholders(q):
    return (q.replace("%7Bdevice_id%7D", "{device_id}")
             .replace("%7Binstall_id%7D", "{install_id}")
             .replace("%7Bsecret_key%7D", "{secret_key}"))


def encode_query(items):
    """Go 的 encodeQuery：排序 + 转义 + 设备占位符还原。"""
    return restore_placeholders(sorted_query(items))


def build_upstream_url(host, path, params):
    base = host.rstrip("/") + "/" + path.lstrip("/")
    if not params:
        return base
    return base + "?" + encode_query(params)


# ===========================================================================
# X-Gorgon（8404 方案；上游已废弃，仅注册链路仍携带）
# ===========================================================================
def generate_x_gorgon(param, ts=None, rnd=None):
    if ts is None:
        ts = now_secs()
    if rnd is None:
        rnd = _os.urandom(2)
    time_bytes = (ts & 0xFFFFFFFF).to_bytes(4, "big")
    md5_prefix = md5_digest(param.encode("utf-8"))[:4]
    data = bytearray(md5_prefix + bytes([0, 0, 0, 0, 0, 1, 7, 4]) + time_bytes)
    r1, r2 = rnd[0], rnd[1]
    key = [74, 0, 22, r2, 71, 108, 0, r1]
    table = list(range(256))
    j = 0
    for i in range(256):
        j = (j + table[i] + key[i & 7]) & 0xFFFFFFFF
        j &= 255
        table[i] = table[j]
    dlen = len(data)
    k = 0
    for i in range(1, dlen + 1):
        idx = ((((i - 1) ^ 1) + ((i - 1) & 1)) << 1) & 255
        table_val = table[idx]
        xor_val = k ^ table_val
        k = (((k | table_val) << 1) - xor_val) & 0xFFFFFFFF
        idx2 = k & 255
        table_val2 = table[idx2]
        table[idx] = table_val2
        table[idx2] = table_val2
        enc_idx = ((table_val2 | table_val2) + (table_val2 & table_val2)) & 255
        data[i - 1] = (data[i - 1] ^ table[enc_idx]) & 0xFF
    w2, w3, w4 = 0xFFFFFFAA, 85, 51
    len_inv = (~dlen) & 0xFFFFFFFF
    for i in range(1, dlen + 1):
        val = data[i - 1]
        val = ((val >> 4) & 15) | ((val & 15) << 4)
        data[i - 1] = val & 0xFF
        if i == dlen:
            data[i - 1] = (val ^ data[0]) & 0xFF
        else:
            nxt = data[i]
            data[i - 1] = ((val | nxt) - (val & nxt)) & 0xFF
        val = data[i - 1]
        t1 = w2 & (val << 1)
        t2 = w3 & (val >> 1)
        val = t1 | t2
        t3 = val << 2
        t4 = w4 & (val >> 2)
        mix = (t3 & 0xFFFFFFCF) | t4
        high = (mix >> 4) & 15
        low = mix & 0x0FFFFFFF
        mix = (low << 4) | high
        val = mix ^ len_inv
        data[i - 1] = val & 0xFF
    out = bytes([132, 4, rnd[0], rnd[1], 0, 0]) + bytes(data)
    return out.hex()


# ===========================================================================
# 设备注册加密原语（device/crypto.rs）
# ===========================================================================
TT_FIXED_STRING_B64 = "TdTC5rgxYgkOUrPHpnM7pByyRiuCmrWKGWs521cXdST0m69/COjWjSanLjfBqVovHwWlGJKu8pSXMrYqOKrdWA=="
TT_MAGIC = bytes([0x74, 0x63, 0x05, 0x10, 0x00, 0x00])
REGISTER_KEY_MASTER_HEX = "ac25c67ddd8f38c1b37a2348828e222e"
REGISTER_KEY_REQ_KEY_B64 = "rCXGfd2POMGzeiNIgo4iLg=="


def tt_encrypt(data, random_bytes32=None):
    """magic + random32 + AES-128-CBC(PKCS7(SHA512(data)+data))。
    key/iv = SHA512(SHA512(random32)+fixed)[0:16]/[16:32]。"""
    if random_bytes32 is None:
        random_bytes32 = _os.urandom(32)
    fixed = base64.b64decode(TT_FIXED_STRING_B64)
    inner = sha512(random_bytes32)
    hv = sha512(inner + fixed)
    aes_key, aes_iv = hv[0:16], hv[16:32]
    hashed_data = sha512(data) + bytes(data)
    padded = pkcs7_pad(hashed_data, 16)
    return TT_MAGIC + bytes(random_bytes32) + aes_cbc_encrypt(padded, aes_key, aes_iv)


def decrypt_register_key(encrypted_key_b64):
    """registerkey 响应 data.key -> 16 字节 secret_key 原文。"""
    data = base64.b64decode(encrypted_key_b64)
    if len(data) < 16:
        raise ValueError("registerkey data too short")
    key = bytes.fromhex(REGISTER_KEY_MASTER_HEX)
    iv, ct = data[:16], data[16:]
    if not ct or len(ct) % 16 != 0:
        raise ValueError("registerkey ciphertext invalid")
    pt = aes_cbc_decrypt(ct, key, iv)
    pad = pt[-1]
    if not (1 <= pad <= 16) or pt[-pad:] != bytes([pad]) * pad:
        raise ValueError("registerkey padding invalid")
    return pt[:-pad]


def reverse_hex(device_id):
    """十进制 id 左补零到 32 位十六进制后按字节对反转。"""
    s = str(device_id)
    if not s.isdigit():
        raise ValueError("device_id is not numeric: %r" % s)
    h = ("%032x" % int(s)).encode("ascii")
    out = bytearray()
    i = len(h)
    while i >= 2:
        out.append(h[i - 2])
        out.append(h[i - 1])
        i -= 2
    return out.decode("ascii")


def encrypt_register_key_request(device_id, iv=None):
    """base64(iv + AES-128-CBC-PKCS7(hex2bin(reverseHex(deviceId))))."""
    key = base64.b64decode(REGISTER_KEY_REQ_KEY_B64)
    if len(key) != 16:
        raise ValueError("registerkey req key len")
    if iv is None:
        iv = _os.urandom(16)
    raw = bytes.fromhex(reverse_hex(device_id))
    padded = pkcs7_pad(raw, 16)
    enc = aes_cbc_encrypt(padded, key, bytes(iv))
    return base64.b64encode(bytes(iv) + enc).decode("ascii")


# ===========================================================================
# 设备身份 DevInfo 与注册流程（device/register.rs）
# ===========================================================================
PKG_NAME = "com.dragon.read"
SDK_VERSION = "v04.04.05-ov-android"
TT_NET = "TTNetVersion:9ac8d95c 2024-11-25 QuicVersion:3f326df4 2024-11-14"


class DevInfo(object):
    def __init__(self):
        self.device_type = "MI 12"
        self.os_api = "29"
        self.os_version = "10"
        self.openudid = random_hex_lower(16)
        self.resolution = "1440*2392"
        self.dpi = "560"
        self.cdid = uuid_v4()
        self.uuid = uuid_v4()
        self.clientudid = uuid_v4()
        self.rom = "EMUI-" + random_alnum(13)
        self.rom_version = random_alnum(2)
        self.device_brand = "Xiaomi"
        self.channel = "xiaomi_1967_64"
        self.version_code = "65132"
        self.version_name = "6.5.1.32"
        self.manifest_version_code = "65132"
        self.update_version_code = "65132"
        self.user_agent = ("com.dragon.read/%s (Linux; U; Android %s; zh_CN; %s; "
                           "Build/MMB29M; Cronet/%s)" %
                           (self.manifest_version_code, self.os_version,
                            self.device_type, TT_NET))

    def url_params(self, extra=None):
        p = [
            ("tt_data", "a"),
            ("os_api", self.os_api),
            ("device_type", self.device_type),
            ("ssmix", "a"),
            ("manifest_version_code", self.manifest_version_code),
            ("dpi", self.dpi),
            ("version_name", self.version_name),
            ("ts", str(now_secs())),
            ("cpu_support64", "true"),
            ("app_type", "normal"),
            ("appTheme", "light"),
            ("ac", "wifi"),
            ("host_abi", "arm64-v8a"),
            ("update_version_code", self.update_version_code),
            ("channel", self.channel),
            ("_rticket", str(now_millis())),
            ("device_platform", "android"),
            ("version_code", self.version_code),
            ("cdid", self.cdid),
            ("os", "android"),
            ("is_android_pad", "0"),
            ("openudid", self.openudid),
            ("package", PKG_NAME),
            ("resolution", self.resolution),
            ("os_version", self.os_version),
            ("language", "zh"),
            ("device_brand", self.device_brand),
            ("need_personal_recommend", "1"),
            ("aid", "1967"),
            ("minor_status", "0"),
            ("app_name", "novel"),
            ("mcc_mnc", "46007"),
        ]
        for k, v in (extra or []):
            p = [(pk, pv) for pk, pv in p if pk != k]
            p.append((k, v))
        return p


class Device(object):
    def __init__(self, device_id="", install_id="", secret_key="", cdid="", openudid=""):
        self.device_id = device_id
        self.install_id = install_id
        self.secret_key = secret_key
        self.cdid = cdid
        self.openudid = openudid

    def to_dict(self):
        return {
            "device_id": self.device_id,
            "install_id": self.install_id,
            "secret_key": self.secret_key,
            "cdid": self.cdid,
            "openudid": self.openudid,
        }

    @classmethod
    def from_dict(cls, d):
        return cls(
            device_id=str(d.get("device_id") or ""),
            install_id=str(d.get("install_id") or ""),
            secret_key=str(d.get("secret_key") or ""),
            cdid=str(d.get("cdid") or ""),
            openudid=str(d.get("openudid") or ""),
        )


# ===========================================================================
# 签名管理（sign/mod.rs Manager）
# ===========================================================================
class SignManager(object):
    def __init__(self):
        self.aid = 1967
        self.license_id = 1611921764
        self.enable_gorgon = False

    def aid_from_query(self, query_string):
        if query_string:
            v = _query_param(query_string, "aid")
            if v is not None and v != "":
                try:
                    return int(v)
                except Exception:
                    pass
        return self.aid

    def generate_headers(self, query_string, post_data=None, opts=None):
        opts = opts or {}
        ts = now_secs()
        ladon_random = _os.urandom(4)
        argus_rand = opts.get("argus_rand")
        if argus_rand is None:
            argus_rand = _random.randint(-(2 ** 31), 2 ** 31 - 1)
        aid = self.aid_from_query(query_string)

        stub_hex = ""
        if not opts.get("skip_stub"):
            src = opts.get("stub_body", post_data)
            if src:
                stub_hex = md5_hex(bytes(src))

        headers = []
        headers.append(("x-ss-req-ticket", str(ts * 1000)))
        headers.append(("x-khronos", str(ts)))
        if not opts.get("skip_ladon"):
            headers.append(("x-ladon", ladon_encrypt(ts, self.license_id, aid, ladon_random)))
        if not opts.get("skip_argus"):
            headers.append(("x-argus", argus_get_sign(
                query_string, stub_hex, ts, aid, self.license_id,
                _query_param(query_string, "device_id") or "",
                opts.get("install_id_field16") or "",
                argus_rand)))
        if stub_hex:
            headers.append(("x-ss-stub", stub_hex))
        if self.enable_gorgon:
            headers.append(("x-gorgon", generate_x_gorgon(query_string)))
        return headers


# ===========================================================================
# 上游 HTTP 客户端（upstream/client.rs）
# ===========================================================================
DEFAULT_USER_AGENT = ("com.dragon.read/66732 (Linux; U; Android 10; zh_CN; Pixel 4 XL; "
                      "Build/QD1A.190821.007;tt-ok/3.12.13.4-tiktok)")


class DeviceFailed(Exception):
    pass


class HttpError(Exception):
    pass


def substitute_device(raw_url, dev):
    openudid = dev.openudid if dev.openudid else dev.device_id
    return (raw_url
            .replace("{device_id}", dev.device_id)
            .replace("{install_id}", dev.install_id)
            .replace("{secret_key}", dev.secret_key)
            .replace("{cdid}", dev.cdid)
            .replace("{openudid}", openudid))


class UpstreamClient(object):
    def __init__(self, store, sign):
        self.store = store
        self.sign = sign
        self.max_retries = 3

    # ---- 底层发送：精确控制头部，不引入额外默认头 ----
    def _send(self, method, url, body, headers, timeout):
        parts = _urlparse.urlsplit(url)
        conn = _httpclient.HTTPSConnection(parts.hostname, parts.port or 443,
                                           timeout=timeout)
        try:
            path = parts.path or "/"
            if parts.query:
                path += "?" + parts.query
            conn.request(method, path, body=body, headers=dict(headers or {}))
            resp = conn.getresponse()
            data = resp.read()
            rh = [(k.lower(), v) for k, v in resp.getheaders()]
            return resp.status, rh, data
        finally:
            try:
                conn.close()
            except Exception:
                pass

    def do_resp(self, method, url, body, headers, no_sign, timeout=15):
        parts = _urlparse.urlsplit(url)
        hdrs = [("User-Agent", DEFAULT_USER_AGENT)]
        for k, v in (headers or []):
            hdrs = [(hk, hv) for hk, hv in hdrs if hk.lower() != k.lower()]
            hdrs.append((k, v))
        if not no_sign:
            sig = self.sign.generate_headers(parts.query or "", body)
            for k, v in sig:
                hdrs = [(hk, hv) for hk, hv in hdrs if hk.lower() != k.lower()]
                hdrs.append((k, v))
        try:
            status, rh, data = self._send(method, url, body, hdrs, timeout)
        except Exception as e:
            raise DeviceFailed("network: %s" % e)
        data = maybe_gunzip(data, rh)
        if status != 200:
            if status in (401, 403):
                raise DeviceFailed("HTTP %d" % status)
            raise HttpError("HTTP %d" % status)
        return data, rh

    def do_with_device(self, method, url, body=None, headers=None, timeout=15):
        """DeviceSigned：取设备 -> 替换占位符 -> 签名 -> 发送；设备类失败换设备重试。"""
        last = None
        for _attempt in range(self.max_retries):
            dev = self.store.get()
            target = substitute_device(url, dev)
            try:
                data, _ = self.do_resp(method, target, body, headers, False, timeout)
                return data
            except DeviceFailed as e:
                last = e
                self.store.invalidate()
                _time.sleep(0.1)
                continue
        raise last if last else RuntimeError("device request failed")

    def do_request(self, method, url, body=None, headers=None, timeout=15):
        """Signed/NoSign：不取设备、不替换占位符。"""
        data, _ = self.do_resp(method, url, body, headers, False, timeout)
        return data


# ===========================================================================
# 设备存储：配置直填 > 文件缓存 > 在线注册
# ===========================================================================
def _device_cache_path():
    """设备缓存路径：环境变量 > 源文件同目录 > cwd > 临时目录（逐个探测可写）。"""
    env = _os.environ.get("FQBOX_DEVICE")
    if env:
        return env
    candidates = []
    try:
        base = _os.path.dirname(_os.path.abspath(__file__))
        candidates.append(_os.path.join(base, "fqbox_device.json"))
    except NameError:
        pass
    try:
        candidates.append(_os.path.join(_os.getcwd(), "fqbox_device.json"))
    except Exception:
        pass
    try:
        import tempfile as _tf
        candidates.append(_os.path.join(_tf.gettempdir(), "fqbox_device.json"))
    except Exception:
        pass
    for p in candidates:
        try:
            if _os.path.exists(p):
                return p
            with open(p, "a"):
                pass
            return p
        except Exception:
            continue
    return candidates[0] if candidates else "fqbox_device.json"


_REGISTER_COOLDOWN = 30        # 注册失败后的重试冷却（秒）
_REGISTER_WAIT_TIMEOUT = 45    # 等待他人注册完成的上限（注册链路约 2~5s）

class DeviceStore(object):
    def __init__(self):
        self._dev = None
        self._custom = None
        self._last_attempt = 0.0
        self.cache_path = _device_cache_path()
        # 并发保护：清缓存/首次安装时多个请求线程会同时触发注册，
        # 旧实现会让其余线程撞 30s cooldown 直接失败（表现为「分类一片空白」）。
        # 现在：注册进行中的线程会等待同一结果，而不是抛错。
        self._lock = _threading_module.RLock()
        self._registering = False
        self._reg_done = _threading_module.Event()

    def set_custom(self, d):
        self._custom = d

    def get(self):
        if self._dev is not None:
            return self._dev
        if self._custom:
            self._dev = Device.from_dict(self._custom)
            return self._dev
        d = self._load_cache()
        if d is not None:
            self._dev = d
            return self._dev
        with self._lock:
            if self._dev is not None:          # 双检：别的线程可能刚好注册完
                return self._dev
            if self._registering:              # 注册进行中：等它的结果
                wait = True
            else:
                self._registering = True
                self._reg_done.clear()
                wait = False
        if wait:
            self._reg_done.wait(_REGISTER_WAIT_TIMEOUT)
            if self._dev is not None:
                return self._dev
            raise RuntimeError("device register timeout")
        try:
            now = _time.time()
            if now - self._last_attempt < _REGISTER_COOLDOWN:
                raise RuntimeError("device register cooldown")
            self._last_attempt = now
            dev = Registrar().register()
            self._dev = dev
            self._save_cache(dev)
            return dev
        finally:
            with self._lock:
                self._registering = False
            self._reg_done.set()

    def invalidate(self):
        self._dev = None
        try:
            _os.remove(self.cache_path)
        except Exception:
            pass

    def _load_cache(self):
        try:
            with open(self.cache_path, "r", encoding="utf-8") as f:
                d = _json.load(f)
            dev = Device.from_dict(d)
            if dev.device_id and dev.install_id:
                return dev
        except Exception:
            pass
        return None

    def _save_cache(self, dev):
        try:
            with open(self.cache_path, "w", encoding="utf-8") as f:
                _json.dump(dev.to_dict(), f)
        except Exception:
            pass


# ===========================================================================
# 注册流程（device/register.rs Registrar）
# ===========================================================================
class Registrar(object):
    def __init__(self):
        self.sign = SignManager()
        # registerKey 签名带 x-gorgon
        self.sign.enable_gorgon = True

    def register(self):
        di = DevInfo()
        device_id, install_id = self.device_register(di)
        try:
            self.app_alert_check(di, device_id, install_id)
        except Exception:
            pass
        _time.sleep(2)
        try:
            self.activate_premium(device_id, install_id, di.device_type)
        except Exception:
            pass
        try:
            secret_key = self.register_key(device_id, install_id)
        except Exception:
            secret_key = ""
        return Device(device_id, install_id, secret_key, di.cdid, di.openudid)

    def _post(self, url, headers, body, timeout=30):
        return UpstreamClient(None, self.sign).do_resp(
            "POST", url, body, headers, True, timeout)[0]

    def _get(self, url, headers, timeout=30):
        return UpstreamClient(None, self.sign).do_resp(
            "GET", url, None, headers, True, timeout)[0]

    def device_register(self, di):
        gtime = now_millis()
        header = {
            "display_name": "番茄小说",
            "update_version_code": di.update_version_code,
            "manifest_version_code": di.manifest_version_code,
            "aid": 1967,
            "channel": di.channel,
            "package": PKG_NAME,
            "app_version": di.version_name,
            "version_code": di.version_code,
            "sdk_version": SDK_VERSION,
            "sdk_target_version": 29,
            "os": "Android",
            "os_version": di.os_version,
            "os_api": di.os_api,
            "device_model": di.device_type,
            "device_brand": di.device_brand,
            "device_manufacturer": "Google",
            "device_category": "phone",
            "cpu_abi": "arm64-v8a",
            "release_build": uuid_v4(),
            "density_dpi": di.dpi,
            "display_density": "mdpi",
            "resolution": di.resolution.replace("*", "x"),
            "language": "zh",
            "mac": rand_mac(),
            "timezone": 8,
            "access": "wifi",
            "not_request_sender": 0,
            "carrier": "CHINA MOBILE",
            "mcc_mnc": "46007",
            "rom": di.rom,
            "rom_version": di.rom_version,
            "sig_hash": md5_hex(uuid_v4().encode("utf-8")),
            "openudid": di.openudid,
            "clientudid": di.clientudid,
            "sim_serial_number": [],
            "region": "CN",
            "tz_name": "Asia/Shanghai",
            "tz_offset": 28800,
            "sim_region": "cn",
        }
        body = {"magic_tag": "ss_app_log", "header": header, "_gen_time": gtime}
        json_data = _json.dumps(body, separators=(",", ":")).encode("utf-8")
        post_data = tt_encrypt(gzip_compress(json_data))

        params = di.url_params([])
        req_url = "https://log.snssdk.com/service/2/device_register/?" + sorted_query(params)
        headers = [
            ("content-type", "application/octet-stream;tt-data=a"),
            ("accept-encoding", "gzip"),
            ("user-agent", di.user_agent),
            ("host", "log.snssdk.com"),
            ("connection", "Keep-Alive"),
        ]
        raw = self._post(req_url, headers, post_data)
        rd = _json.loads(raw.decode("utf-8", "replace"))
        device_id = _pick_str(rd, ["device_id_str", "device_id"])
        install_id = _pick_str(rd, ["install_id_str", "install_id"])
        if not device_id or not install_id:
            raise RuntimeError("bad device_register response: %r" % raw[:200])
        return device_id, install_id

    def app_alert_check(self, di, device_id, install_id):
        params = di.url_params([
            ("device_id", device_id),
            ("iid", install_id),
        ])
        query = sorted_query(params)
        req_url = "https://ichannel.snssdk.com/service/2/app_alert_check/?" + query
        headers = [
            ("content-type", "application/octet-stream;tt-data=a"),
            ("accept-encoding", "gzip"),
            ("log-encode-type", "gzip"),
            ("x-tt-request-tag", "t=0;n=1"),
            ("x-ss-req-ticket", str(now_millis())),
            ("sdk-version", "2"),
            ("passport-sdk-version", di.version_code),
            ("x-vc-bdturing-sdk-version", "3.7.4.cn"),
            ("user-agent", di.user_agent),
            ("host", "ichannel.snssdk.com"),
            ("connection", "Keep-Alive"),
        ]
        for k, v in self.sign.generate_headers(query, None):
            headers = [(hk, hv) for hk, hv in headers if hk.lower() != k.lower()]
            headers.append((k, v))
        try:
            self._get(req_url, headers)
        except Exception:
            pass

    def activate_premium(self, device_id, install_id, device_type):
        parts = sorted([
            "aid=1967",
            "app_name=novelapp",
            "channel=0",
            "device_id=%s" % device_id,
            "device_platform=android",
            "device_type=%s" % device_type,
            "iid=%s" % install_id,
            "os_version=0",
            "version_code=61532",
            "version_name=6.1.5.32",
            "manifest_version_code=61532",
            "update_version_code=61532",
        ])
        req_url = ("https://api5-normal-sinfonlinea.fqnovel.com/reading/user/privilege/add/v/?"
                   + "&".join(parts))
        body = _json.dumps({
            "add_count_daily": 0,
            "amount": 2592000,
            "privilege_id": 7210376203117531962,
            "from": 8,
            "unique_key": str(now_millis()),
        }, separators=(",", ":")).encode("utf-8")
        try:
            self._post(req_url, [], body)
        except Exception:
            pass

    def register_key(self, device_id, install_id):
        content = encrypt_register_key_request(device_id)
        parts = sorted([
            "aid=1967",
            "app_name=novelapp",
            "channel=0",
            "device_id=%s" % device_id,
            "device_platform=android",
            "iid=%s" % install_id,
            "os_version=0",
            "version_code=6.1.5.32",
            "version_name=6.1.5.32",
        ])
        param_string = "&".join(parts)
        req_url = "https://reading.snssdk.com/reading/crypt/registerkey?" + param_string
        post_json = _json.dumps({"content": content}, separators=(",", ":")).encode("utf-8")
        compressed = gzip_compress(post_json)
        sig_headers = self.sign.generate_headers(param_string, compressed)

        last_err = ""
        for _attempt in range(3):
            headers = [("User-Agent", "com.dragon.read"), ("Content-Encoding", "gzip")]
            for k, v in sig_headers:
                headers = [(hk, hv) for hk, hv in headers if hk.lower() != k.lower()]
                headers.append((k, v))
            try:
                raw = self._post(req_url, headers, compressed)
            except Exception as e:
                last_err = str(e)
                _time.sleep(1)
                continue
            try:
                rd = _json.loads(raw.decode("utf-8", "replace"))
            except Exception as e:
                last_err = "json: %s" % e
                _time.sleep(1)
                continue
            key = ""
            try:
                key = rd["data"]["key"] or ""
            except Exception:
                key = ""
            if not key:
                last_err = "missing key field"
                _time.sleep(1)
                continue
            dec = decrypt_register_key(key)
            if dec:
                return dec.hex().upper()
            last_err = "decrypt key: empty"
            _time.sleep(1)
        raise RuntimeError("register_key failed: %s" % last_err)


def _pick_str(v, keys):
    for k in keys:
        val = v.get(k) if isinstance(v, dict) else None
        if isinstance(val, str) and val:
            return val
        if val is not None and not isinstance(val, (dict, list, bool)):
            s = str(val)
            if s:
                return s
    return ""


# ===========================================================================
# 上游常量（endpoints/base.rs）
# ===========================================================================
HOST_FQNOVEL = "https://api5-normal-sinfonlineb.fqnovel.com"
HOST_FQNOVELA = "https://api5-normal-sinfonlinea.fqnovel.com"
HOST_NOVEL_SNSSDK = "https://novel.snssdk.com"
HOST_READING_SNSSDK = "https://reading.snssdk.com"
HOST_FANQIENOVEL = "https://fanqienovel.com"
UA_DRAGON = "com.dragon.read"
CONTENT_TYPE_JSON = "application/json; charset=utf-8"


def dragon_read_headers():
    return [("User-Agent", UA_DRAGON)]


def dragon_read_json_headers():
    return [
        ("User-Agent", UA_DRAGON),
        ("Content-Type", CONTENT_TYPE_JSON),
    ]


def phoenix_player_headers():
    return [
        ("User-Agent",
         "com.phoenix.read/71332 (Linux; U; Android 16; zh_CN; 25053RT47C; "
         "Build/BP2A.250605.031.A3; Cronet/TTNetVersion:04657795 2026-01-23 "
         "QuicVersion:c67e9834 2025-09-08)"),
        ("Accept", "application/json; charset=utf-8,application/x-protobuf"),
        ("Content-Type", "application/json"),
        ("x-xs-from-web", "0"),
        ("sdk-version", "2"),
    ]


def phoenix_player_url():
    return ("%s/novel/player/multi_video_model/v1/?iid={install_id}"
            "&device_id={device_id}&ac=wifi&channel=update_64&aid=8662"
            "&app_name=novelread&version_code=71332&version_name=7.1.3.32"
            "&device_platform=android&os=android&ssmix=a&device_type=25053RT47C"
            "&device_brand=Redmi&language=zh&os_api=36&os_version=16"
            "&manifest_version_code=71332&resolution=1280*2772&dpi=520"
            "&update_version_code=71332&host_abi=arm64-v8a&dragon_device_type=phone"
            "&pv_player=71332&compliance_status=0&need_personal_recommend=1"
            "&player_so_load=1&is_android_pad_screen=0" % HOST_FQNOVEL)


SHORTPLAY_VIDEO_MODEL_URL = ("https://api3-normal-sinfonlinea.fqnovel.com/novel/player/video_model/v1/"
                             "?iid={install_id}&device_id={device_id}&aid=1967&app_name=novelapp"
                             "&version_code=72132&version_name=7.2.1.32&device_platform=android"
                             "&device_brand=Xiaomi&os_version=13&cdid={cdid}")
VIDEO_DETAIL_PATH = "/novel/player/video_detail/v1/"
UA_WINDOWS_BROWSER = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
FALLBACK_USER_AGENT = ("com.xs.fm/632 (Linux; U; Android 15; zh_CN; 23049RAD8C; "
                       "Build/AQ3A.250226.002; Cronet/TTNetVersion:fc4cebd3 2024-12-10 "
                       "QuicVersion:d9628e3d 2024-10-11)")


def video_detail_url():
    return phoenix_player_url().replace("/novel/player/multi_video_model/v1/", VIDEO_DETAIL_PATH, 1)


# ===========================================================================
# spade 直链解密（endpoints/video.rs）
# ===========================================================================
SPADE_CONSTANTS = bytes([
    77, 212, 194, 230, 184, 49, 98, 9, 14, 82, 179, 199, 166, 115, 59, 164,
    28, 178, 70, 43, 130, 154, 181, 138, 25, 107, 57, 219, 87, 23, 117, 36,
    244, 155, 175, 127, 8, 232, 214, 141, 38, 167, 46, 55, 193, 169, 90, 47,
    31, 5, 165, 24, 146, 174, 242, 148, 151, 50, 182, 42, 56, 170, 221, 88,
])


def audio_b64_decode(s):
    """容忍缺 padding 的 base64 解码。"""
    trimmed = str(s or "").strip()
    pad = (4 - len(trimmed) % 4) % 4
    padded = trimmed + "=" * pad
    cleaned = "".join(c for c in padded if c != "\r" and c != "\n")
    try:
        return base64.b64decode(cleaned)
    except Exception:
        return b""


def bit_count(n):
    return bin(n).count("1")


def decrypt_spade_url(value, key_seed):
    if not value:
        return ""
    raw = audio_b64_decode(value)
    if len(raw) < 5 or raw[0] != 168 or raw[2] != 1 or raw[3] != 0:
        return value
    cipher_data = raw[4:]
    cipher_len = len(cipher_data) // 16 * 16
    cipher_data = cipher_data[:cipher_len]
    if not cipher_data:
        return value
    h1 = sha512(bytes(key_seed))
    seed = h1 + SPADE_CONSTANTS
    h2 = sha512(seed)
    out = aes_cbc_decrypt(cipher_data, h2[0:16], h2[16:32])
    try:
        out = pkcs7_unpad(out, 16)
    except Exception:
        pass
    return out.decode("utf-8", "replace").rstrip("\x00")


def derive_spade_content_key(value):
    """spade_a -> 16 字节内容密钥（hex 字符串形式藏在变体里）。"""
    if not value:
        return b""
    raw = audio_b64_decode(value)
    if len(raw) < 3:
        return b""
    out_len = len(raw) - (raw[0] ^ raw[1] ^ raw[2]) + 0x2F
    if out_len < 33 or out_len + 1 > len(raw):
        return b""
    buf = bytearray(raw[1:1 + out_len])
    src = bytes(buf)
    prev_a = 0x55
    prev_b = 0xF6
    for i, cur in enumerate(src):
        if i & 1 == 1:
            keep = cur
        else:
            keep = prev_a
            prev_a = prev_b
            prev_b = cur
        buf[i] = (((prev_a ^ cur) - bit_count(i) - 0x15) & 0xFF)
        prev_a = keep
    key_hex = buf[1:33].decode("utf-8", "replace")
    try:
        key = bytes.fromhex(key_hex)
    except Exception:
        return b""
    return key if len(key) == 16 else b""


# ---- 响应解析工具 ----
def strip_control_chars(b):
    out = bytearray()
    for c in bytes(b):
        if c <= 0x08 or c == 0x0B or c == 0x0C or (0x0E <= c <= 0x1F) or c == 0x7F:
            continue
        out.append(c)
    return bytes(out)


def _as_map(v):
    return v if isinstance(v, dict) else None


def _int64_from_any(v):
    if isinstance(v, bool):
        return 0
    if isinstance(v, int):
        return v
    if isinstance(v, float):
        return int(v)
    if isinstance(v, str):
        return _scan_i64(v)
    return 0


def _scan_i64(s):
    t = s.strip()
    sign = 1
    i = 0
    if t and t[0] in "+-":
        if t[0] == "-":
            sign = -1
        i = 1
    digits = []
    while i < len(t) and t[i].isdigit():
        digits.append(t[i])
        i += 1
    if not digits:
        return 0
    return sign * int("".join(digits))


def variant_display_name(height):
    if height <= 0:
        return ""
    if height <= 360:
        return "360P"
    if height <= 480:
        return "480P"
    if height <= 540:
        return "540P"
    if height <= 720:
        return "720P"
    if height <= 1080:
        return "1080P"
    if height <= 1440:
        return "2K"
    return "4K"


def video_quality_score(info):
    codec = ""
    v = info.get("codec_type")
    if isinstance(v, str):
        codec += v.lower()
    meta = _as_map(info.get("video_meta"))
    if meta:
        v = meta.get("codec_type")
        if isinstance(v, str):
            codec += " " + v.lower()
    v = info.get("gear_des_key")
    if isinstance(v, str):
        codec += " " + v.lower()
    if "bytevc2" in codec:
        return None
    w = _int64_from_any(info.get("vwidth"))
    h = _int64_from_any(info.get("vheight"))
    b = _int64_from_any(info.get("bitrate"))
    if b == 0:
        b = _int64_from_any(info.get("real_bitrate"))
    bonus = 1 if ("h264" in codec or "avc1" in codec) else 0
    return w * 1000000000 + h * 1000000 + b + bonus


def _decode_video_model(v):
    if isinstance(v, dict):
        return v
    if isinstance(v, str):
        try:
            j = _json.loads(v)
            if isinstance(j, dict):
                return j
        except Exception:
            return None
    return None


def video_models(data):
    """data.video_model（对象或 JSON 字符串）优先，其次各子项的 video_model。"""
    out = []
    top = data.get("video_model")
    if top is not None:
        m = _decode_video_model(top)
        if m is not None:
            out.append(m)
    for item in data.values():
        if isinstance(item, dict):
            m = _decode_video_model(item.get("video_model"))
            if m is not None:
                out.append(m)
    return out


def decrypt_variant_entry(info, key_seed):
    """一条 video_list 档位 -> (可播放 URL, 内容密钥)。"""
    if not key_seed:
        return None
    raw_url = info.get("main_url") if isinstance(info.get("main_url"), str) else ""
    if not raw_url:
        raw_url = info.get("backup_url_1") if isinstance(info.get("backup_url_1"), str) else ""
    if raw_url and not raw_url.startswith("http"):
        dec = audio_b64_decode(raw_url)
        if dec.startswith(b"http"):
            raw_url = dec.decode("utf-8", "replace")
    u = decrypt_spade_url(raw_url, key_seed)
    if not u:
        return None
    spade_a = info.get("spade_a") if isinstance(info.get("spade_a"), str) else ""
    return u, derive_spade_content_key(spade_a)


def select_video_source(variants, resolve):
    """按画质打分降序选第一个能解出 URL 的档；全被编码门拒 -> CodecRejected。"""
    unresolved = "notfound"
    infos = []
    for v in variants:
        info = _as_map(v)
        if info is None:
            continue
        score = video_quality_score(info)
        if score is None:
            unresolved = "codec"
            continue
        infos.append((score, info))
    infos.sort(key=lambda t: t[0], reverse=True)
    for _score, info in infos:
        r = resolve(info)
        if r is not None:
            return "found", r
    return unresolved, None


def fallback_api_url(model):
    u = ""
    f = model.get("fallback_api")
    if isinstance(f, dict):
        u = f.get("fallback_api") if isinstance(f.get("fallback_api"), str) else ""
    elif isinstance(f, str):
        try:
            m = _json.loads(f)
            if isinstance(m, dict) and isinstance(m.get("fallback_api"), str):
                u = m["fallback_api"]
        except Exception:
            pass
        if not u:
            u = f
    u = u.replace("&stream_type=audio_encrypt", "")
    u = u.replace("?stream_type=audio_encrypt&", "?")
    return u


_FPLAY_CODEC_TYPE_RE = _re.compile(r"([?&])codec_type=\d+")


def prefer_h265_fallback_url(url):
    """fplay URL 的 codec_type：3/4=bytevc1，0/1/2=h265。改成 1 优先拿 h265 档。"""
    if not url or "codec_type=" not in url:
        return url
    return _FPLAY_CODEC_TYPE_RE.sub(r"\1codec_type=1", url, count=1)


def extract_video_list_source(video_list):
    """旧式明文 video_list（play_url/main_url，无 spade）。"""
    return select_video_source(list(reversed(video_list)), lambda info: (
        next((u for u in (info.get("play_url"), info.get("main_url"))
              if isinstance(u, str) and u), None), b""))


def video_model_encrypted(model):
    vl = model.get("video_list")
    if not isinstance(vl, list):
        return False
    for item in vl:
        info = _as_map(item)
        if info is None:
            continue
        ei = _as_map(info.get("encrypt_info"))
        if ei and ei.get("encrypt") is True:
            return True
    return False


def extract_video_model_url(model):
    vl = model.get("video_list")
    if not isinstance(vl, list):
        return "notfound", None
    return extract_video_list_source(vl)


def extract_video_info_list_map_url(data):
    vm = _as_map(data.get("video_info_list_map"))
    if vm is None:
        return "notfound", None
    video_list = None
    for v in vm.values():
        if isinstance(v, list) and v:
            video_list = v
            break
    if video_list is None:
        return "notfound", None
    info = _as_map(video_list[0])
    if info is None:
        return "notfound", None
    pil = info.get("play_info_list")
    if not isinstance(pil, list):
        return "notfound", None
    return extract_video_list_source(pil)


def extract_shortplay_video_model_source(model):
    video_list = _as_map(model.get("video_list"))
    if video_list is None:
        return "notfound", None
    ks = model.get("key_seed")
    key_seed = None
    if isinstance(ks, str) and ks:
        key_seed = audio_b64_decode(ks)
    return select_video_source(list(video_list.values()),
                               lambda info: decrypt_variant_entry(info, key_seed))


def variant_rows_scored(video_list, key_seed):
    rows = []
    if not isinstance(video_list, dict):
        return rows
    for slot, value in video_list.items():
        info = _as_map(value)
        if info is None:
            continue
        w = _int64_from_any(info.get("vwidth"))
        h = _int64_from_any(info.get("vheight"))
        short_edge = min(w, h) if (w > 0 and h > 0) else max(w, h)
        name = variant_display_name(short_edge)
        score = video_quality_score(info)
        if score is None:
            continue
        r = decrypt_variant_entry(info, key_seed)
        if r is None:
            continue
        url, key = r
        rows.append((score, {
            "name": name, "width": w, "height": h,
            "url": url, "key_hex": key.hex(),
        }))
    rows.sort(key=lambda t: t[0], reverse=True)
    return rows


def merge_variant_rows(scored):
    """按 name 去重（先到先得），再按画质分降序。"""
    seen = set()
    out = []
    for score, row in scored:
        name = row.get("name") or ""
        if not name or name in seen:
            continue
        seen.add(name)
        out.append((score, row))
    out.sort(key=lambda t: t[0], reverse=True)
    return [row for _score, row in out]


# ===========================================================================
# FqBox 客户端：所有上游端点
# ===========================================================================
def _reading724_params():
    return [
        ("iid", "{install_id}"),
        ("device_id", "{device_id}"),
        ("ac", "wifi"),
        ("channel", "xiaomi_1967_64"),
        ("aid", "1967"),
        ("app_name", "novelapp"),
        ("version_code", "72432"),
        ("version_name", "7.2.4.32"),
        ("device_platform", "android"),
        ("os", "android"),
        ("ssmix", "a"),
        ("device_type", "25053RT47C"),
        ("device_brand", "Redmi"),
        ("language", "zh"),
        ("os_api", "36"),
        ("os_version", "16"),
        ("manifest_version_code", "72432"),
        ("resolution", "1280*2620"),
        ("dpi", "520"),
        ("update_version_code", "72432"),
        ("host_abi", "arm64-v8a"),
        ("dragon_device_type", "phone"),
        ("pv_player", "72432"),
        ("compliance_status", "0"),
        ("need_personal_recommend", "1"),
        ("player_so_load", "1"),
        ("is_android_pad_screen", "0"),
        ("rom_version", "miui_V816_OS3.0.9.0.WOLCNXM"),
    ]


# ===========================================================================
# 正文解密（crypto.rs decrypt_upstream）：b64 -> [iv16][ct] -> AES-CBC -> unpad
# ===========================================================================
def decrypt_upstream(encrypted_b64, secret_key_hex):
    """reading.snssdk.com 正文/漫画内容解密。松散 unpad + gzip 自动解压。"""
    try:
        raw = base64.b64decode(encrypted_b64)
    except Exception as e:
        raise ValueError("base64: %s" % e)
    if len(raw) < 16:
        raise ValueError("ciphertext too short: %d" % len(raw))
    try:
        key = bytes.fromhex(secret_key_hex.strip())
    except Exception:
        raise ValueError("bad secret key")
    if len(key) != 16:
        raise ValueError("bad secret key")
    iv, ct = raw[:16], raw[16:]
    if len(ct) % 16 != 0:
        raise ValueError("ciphertext not block-aligned: %d" % len(ct))
    pt = aes_cbc_decrypt(ct, key, iv)
    if pt:
        pad = pt[-1]
        if 0 < pad <= 16 and pad <= len(pt):
            pt = pt[:len(pt) - pad]
    if len(pt) >= 2 and pt[0] == 0x1f and pt[1] == 0x8b:
        pt = gunzip_bytes(pt)
    return pt


# ===========================================================================
# AES-256-GCM（漫画图片解密，manga.rs decryptMangaImage）
# ===========================================================================
def _aes_key_schedule(key):
    """通用 AES 密钥扩展（128/192/256 位）-> (round_keys, rounds)。"""
    nk = len(key) // 4
    if nk not in (4, 6, 8):
        raise ValueError("bad aes key length")
    nr = {4: 10, 6: 12, 8: 14}[nk]
    w = [list(key[i * 4:i * 4 + 4]) for i in range(nk)]
    total = 4 * (nr + 1)
    rcon = 1
    for i in range(nk, total):
        t = list(w[i - 1])
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [_AES_SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = _aes_xtime(rcon)
        elif nk > 6 and i % nk == 4:
            t = [_AES_SBOX[b] for b in t]
        w.append([w[i - nk][j] ^ t[j] for j in range(4)])
    rk = []
    for r in range(nr + 1):
        rk.append(bytes(b for word in w[r * 4:r * 4 + 4] for b in word))
    return rk, nr


def _aes_encrypt_block_generic(block, rk, nr):
    def add_round_key(state, r):
        return [state[i] ^ r[i] for i in range(16)]

    def sub_shift(state):
        out = [0] * 16
        for c in range(4):
            for r in range(4):
                out[c * 4 + r] = _AES_SBOX[state[((c + r) % 4) * 4 + r]]
        return out

    def mix(state):
        out = [0] * 16
        for c in range(4):
            col = state[c * 4:c * 4 + 4]
            out[c * 4 + 0] = _aes_mul(col[0], 2) ^ _aes_mul(col[1], 3) ^ col[2] ^ col[3]
            out[c * 4 + 1] = col[0] ^ _aes_mul(col[1], 2) ^ _aes_mul(col[2], 3) ^ col[3]
            out[c * 4 + 2] = col[0] ^ col[1] ^ _aes_mul(col[2], 2) ^ _aes_mul(col[3], 3)
            out[c * 4 + 3] = _aes_mul(col[0], 3) ^ col[1] ^ col[2] ^ _aes_mul(col[3], 2)
        return out

    s = add_round_key(list(block), rk[0])
    for rnd in range(1, nr):
        s = sub_shift(s)
        s = mix(s)
        s = add_round_key(s, rk[rnd])
    s = sub_shift(s)
    s = add_round_key(s, rk[nr])
    return bytes(s)


def _gf_mul_128(x, y):
    """GF(2^128) 乘法（GCM 规约多项式，位反射约定）。"""
    z = bytearray(16)
    v = bytearray(y)
    for i in range(128):
        if (x[i // 8] >> (7 - (i % 8))) & 1 == 1:
            for j in range(16):
                z[j] ^= v[j]
        lsb = v[15] & 1
        for j in range(15, 0, -1):
            v[j] = (v[j] >> 1) | ((v[j - 1] & 1) << 7)
        v[0] >>= 1
        if lsb == 1:
            v[0] ^= 0xe1
    return bytes(z)


def _ghash_128(h, data):
    y = bytearray(16)
    for i in range(0, len(data), 16):
        block = data[i:i + 16]
        for j in range(min(16, len(block))):
            y[j] ^= block[j]
        y = bytearray(_gf_mul_128(bytes(y), h))
    return bytes(y)


def _inc32(block):
    b = bytearray(block)
    for i in range(15, 11, -1):
        b[i] = (b[i] + 1) & 0xff
        if b[i] != 0:
            break
    return bytes(b)


_GHASH_TBLS = {}   # H(16 bytes) -> (16 个 256 项 int 表)，小容量缓存


def _ghash_table_ints(h16):
    """GHASH 乘法表：tbl[i][b] = 第 i 字节为 b 的单位块经 GF(2^128) 乘 H。
    利用乘法对 XOR 的双线性，只用 16×8 次 _gf_mul_128 建基，再按位组合。"""
    t = _GHASH_TBLS.get(h16)
    if t is not None:
        return t
    tbl = []
    for i in range(16):
        base = []
        for bit in range(8):
            unit = bytearray(16)
            unit[i] = 1 << bit
            base.append(int.from_bytes(_gf_mul_128(bytes(unit), h16), "big"))
        row = [0] * 256
        for b in range(1, 256):
            acc = 0
            bb = b
            bit = 0
            while bb:
                if bb & 1:
                    acc ^= base[bit]
                bb >>= 1
                bit += 1
            row[b] = acc
        tbl.append(row)
    if len(_GHASH_TBLS) >= 4:
        _GHASH_TBLS.clear()
    _GHASH_TBLS[h16] = tbl
    return tbl


def _ghash_fast(h16, data):
    """表驱动 GHASH，与 _ghash_128 输出逐字节一致。"""
    if not data:
        return b"\x00" * 16
    tbl = _ghash_table_ints(h16)
    y = 0
    n = len(data)
    off = 0
    while off < n:
        blk = data[off:off + 16]
        if len(blk) < 16:
            blk = blk + b"\x00" * (16 - len(blk))
        zb = (int.from_bytes(blk, "big") ^ y).to_bytes(16, "big")
        acc = 0
        for i in range(16):
            acc ^= tbl[i][zb[i]]
        y = acc
        off += 16
    return y.to_bytes(16, "big")


def aes256_gcm_decrypt(data, key):
    """AES-256-GCM：12 字节 nonce 前缀 + 16 字节 tag 后缀，无 AAD。
    后端：pycryptodome -> cryptography -> 纯 Python（T-table 密钥流 + 表驱动 GHASH）。"""
    if len(data) < 28:
        raise ValueError("image too short")
    if len(key) != 32:
        raise ValueError("bad key length")
    iv, tag, ct = data[:12], data[-16:], data[12:-16]
    if _PCD_AES is not None:
        try:
            c = _PCD_AES.new(key, _PCD_AES.MODE_GCM, nonce=iv)
            return c.decrypt_and_verify(ct, tag)
        except ValueError:
            raise ValueError("gcm: authentication failed")
        except Exception:
            pass
    if _CRY_Cipher is not None:
        try:
            from cryptography.exceptions import InvalidTag as _InvTag
            dec = _CRY_Cipher(_CRY_ALG.AES(key),
                              _CRY_MODES.GCM(iv, tag)).decryptor()
            try:
                return dec.update(ct) + dec.finalize()
            except _InvTag:
                raise ValueError("gcm: authentication failed")
        except ValueError:
            raise
        except Exception:
            pass
    # 纯 Python：T-table 连续块加密 + 表驱动 GHASH
    j0 = bytearray(16)
    j0[:12] = iv
    j0[15] = 1
    j0_int = int.from_bytes(bytes(j0), "big")
    h = _aes_encrypt_blocks_fast(bytes(key), 0, 1)
    ghash_in = bytes(ct) + b"\x00" * ((16 - len(ct) % 16) % 16)
    ghash_in += b"\x00" * 8 + (len(ct) * 8).to_bytes(8, "big")
    s = _ghash_fast(h, ghash_in)
    ek = _aes_encrypt_blocks_fast(bytes(key), j0_int, 1)
    expected = bytes(a ^ b for a, b in zip(ek, s))
    if expected != tag:
        raise ValueError("gcm: authentication failed")
    n = len(ct)
    if n == 0:
        return b""
    ks = _aes_encrypt_blocks_fast(bytes(key), (j0_int + 1) & _CTR_MASK128,
                                  (n + 15) // 16)
    return (int.from_bytes(ct, "big") ^
            int.from_bytes(ks[:n], "big")).to_bytes(n, "big")


# ===========================================================================
# CENC / AES-CTR 解密（视频轨、音频轨、流式代理共用）
# 参考 byte-dance fqapp muxer：encv/enca + sinf(tenc) + senc + saiz + saio
# ===========================================================================
_CTR_MASK128 = (1 << 128) - 1

# ---- AES-CTR 后端：pycryptodome / cryptography / 纯 Python T-table ----
try:
    from Crypto.Cipher import AES as _PCD_AES
except Exception:
    _PCD_AES = None
try:
    from cryptography.hazmat.primitives.ciphers import (
        Cipher as _CRY_Cipher, algorithms as _CRY_ALG, modes as _CRY_MODES)
except Exception:
    _CRY_Cipher = None

# T-table（Te0~Te3 + S盒直查），供纯 Python 快速块加密
_TE = None


def _build_te_tables():
    global _TE
    if _TE is not None:
        return _TE
    te0 = [0] * 256
    for x in range(256):
        s = _AES_SBOX[x]
        te0[x] = ((_aes_mul(s, 2) << 24) | (s << 16) | (s << 8) | _aes_mul(s, 3))
    te1 = [((v >> 8) | (v << 24)) & 0xffffffff for v in te0]
    te2 = [((v >> 16) | (v << 16)) & 0xffffffff for v in te0]
    te3 = [((v >> 24) | (v << 8)) & 0xffffffff for v in te0]
    _TE = (te0, te1, te2, te3)
    return _TE


def _aes_encrypt_blocks_fast(key, counter_int, nblocks):
    """连续 nblocks 个 AES 块加密，返回 bytes（16*nblocks）。
    counter_int 为第一个块的 128-bit 计数器值（大端）。"""
    if nblocks <= 0:
        return b""
    total = 16 * nblocks
    if _PCD_AES is not None:
        c = _PCD_AES.new(key, _PCD_AES.MODE_CTR, nonce=b"",
                         initial_value=counter_int.to_bytes(16, "big"))
        return c.encrypt(b"\x00" * total)
    if _CRY_Cipher is not None:
        enc = _CRY_Cipher(_CRY_ALG.AES(key),
                          _CRY_MODES.CTR(counter_int.to_bytes(16, "big"))).encryptor()
        return enc.update(b"\x00" * total) + enc.finalize()
    # 纯 Python T-table
    te0, te1, te2, te3 = _build_te_tables()
    sb = _AES_SBOX
    rk, nr = _aes_key_schedule(key)
    rkw = []
    for r in range(nr + 1):
        b = rk[r]
        rkw.append((int.from_bytes(b[0:4], "big"), int.from_bytes(b[4:8], "big"),
                    int.from_bytes(b[8:12], "big"), int.from_bytes(b[12:16], "big")))
    out = bytearray(total)
    ctr = counter_int & _CTR_MASK128
    # 计数器按 4 个字递进（低位进位；等价对 128-bit 整数递增）
    c0 = (ctr >> 96) & 0xffffffff
    c1 = (ctr >> 64) & 0xffffffff
    c2 = (ctr >> 32) & 0xffffffff
    c3 = ctr & 0xffffffff
    k0 = rkw[0]
    last = nr - 1
    for i in range(nblocks):
        s0 = c0 ^ k0[0]
        s1 = c1 ^ k0[1]
        s2 = c2 ^ k0[2]
        s3 = c3 ^ k0[3]
        for rnd in range(1, nr):
            r0, r1, r2, r3 = rkw[rnd]
            t0 = te0[s0 >> 24] ^ te1[(s1 >> 16) & 0xff] ^ te2[(s2 >> 8) & 0xff] ^ te3[s3 & 0xff] ^ r0
            t1 = te0[s1 >> 24] ^ te1[(s2 >> 16) & 0xff] ^ te2[(s3 >> 8) & 0xff] ^ te3[s0 & 0xff] ^ r1
            t2 = te0[s2 >> 24] ^ te1[(s3 >> 16) & 0xff] ^ te2[(s0 >> 8) & 0xff] ^ te3[s1 & 0xff] ^ r2
            t3 = te0[s3 >> 24] ^ te1[(s0 >> 16) & 0xff] ^ te2[(s1 >> 8) & 0xff] ^ te3[s2 & 0xff] ^ r3
            s0, s1, s2, s3 = t0, t1, t2, t3
        r0, r1, r2, r3 = rkw[last + 1]
        o0 = ((sb[t0 >> 24] << 24) | (sb[(t1 >> 16) & 0xff] << 16) |
              (sb[(t2 >> 8) & 0xff] << 8) | sb[t3 & 0xff]) ^ r0
        o1 = ((sb[t1 >> 24] << 24) | (sb[(t2 >> 16) & 0xff] << 16) |
              (sb[(t3 >> 8) & 0xff] << 8) | sb[t0 & 0xff]) ^ r1
        o2 = ((sb[t2 >> 24] << 24) | (sb[(t3 >> 16) & 0xff] << 16) |
              (sb[(t0 >> 8) & 0xff] << 8) | sb[t1 & 0xff]) ^ r2
        o3 = ((sb[t3 >> 24] << 24) | (sb[(t0 >> 16) & 0xff] << 16) |
              (sb[(t1 >> 8) & 0xff] << 8) | sb[t2 & 0xff]) ^ r3
        p = i * 16
        out[p:p + 4] = o0.to_bytes(4, "big")
        out[p + 4:p + 8] = o1.to_bytes(4, "big")
        out[p + 8:p + 12] = o2.to_bytes(4, "big")
        out[p + 12:p + 16] = o3.to_bytes(4, "big")
        # 先用后递增：第 i 块用 ctr+i
        c3 += 1
        if c3 > 0xffffffff:
            c3 = 0
            c2 += 1
            if c2 > 0xffffffff:
                c2 = 0
                c1 += 1
                if c1 > 0xffffffff:
                    c1 = 0
                    c0 = (c0 + 1) & 0xffffffff
    return bytes(out)


def _ctr_keystream_int(nbytes, key, ctr_int):
    """生成 nbytes 字节 AES-CTR 密钥流，返回一个大整数（高位对齐）。"""
    if nbytes <= 0:
        return 0
    ks = _aes_encrypt_blocks_fast(bytes(key), ctr_int, (nbytes + 15) // 16)
    return int.from_bytes(ks, "big")


def aes_ctr_xor(seg, key, ctr_int):
    """整段 AES-CTR（加解密同式）。ctr_int 为 128-bit 大端计数器初值。"""
    if not seg:
        return b""
    n = len(seg)
    ks = _aes_encrypt_blocks_fast(bytes(key), ctr_int, (n + 15) // 16)
    return (int.from_bytes(seg, "big") ^
            int.from_bytes(ks[:n], "big")).to_bytes(n, "big")


def _ctr_decrypt_region(data, file_off, length, key, base_ctr, region_start):
    """解密 data[file_off:file_off+length]。
    region_start 为区段相对样本起始的偏移（CENC 块计数按整样本连续计，
    含明文区段也占块）。key 为 16/24/32 字节 AES 密钥。"""
    if length <= 0:
        return
    start_block = region_start // 16
    block_off = region_start % 16
    total = block_off + length
    ks = _aes_encrypt_blocks_fast(bytes(key),
                                  (base_ctr + start_block) & _CTR_MASK128,
                                  (total + 15) // 16)
    ks = ks[block_off:block_off + length]
    seg = bytes(data[file_off:file_off + length])
    data[file_off:file_off + length] = (int.from_bytes(seg, "big") ^
                                        int.from_bytes(ks, "big")).to_bytes(length, "big")


def _find_box(data, fourcc, start):
    """从 start 起扫描首个 fourcc 盒子，返回 (offset, size)。"""
    b = fourcc.encode("ascii") if isinstance(fourcc, str) else fourcc
    for i in range(max(start, 4), len(data) - 8):
        if data[i:i + 4] == b:
            sz = int.from_bytes(data[i - 4:i], "big")
            if 0 < sz < 5000000:
                return i - 4, sz
    return -1, 0


def _get_box(data, fourcc, stbl_off):
    o, sz = _find_box(data, fourcc, stbl_off)
    if o >= 0:
        return bytes(data[o + 8:o + sz])
    return None


def _iv_to_ctr(iv, iv_len, constant_iv=b""):
    """CENC 样本 IV -> 128-bit CTR 初值。8 字节 IV 高位对齐补零。"""
    v = iv if iv_len != 0 else (constant_iv or iv)
    if len(v) >= 16:
        return int.from_bytes(bytes(v[:16]), "big")
    if len(v) <= 0:
        return 0
    return int.from_bytes(bytes(v) + b"\x00" * (16 - len(v)), "big")


def _enc_regions(subsamples, sample_sz):
    """需要解密的区间 [(start_in_sample, end_in_sample)]；空 -> 整段加密。"""
    if not subsamples:
        return [(0, sample_sz)]
    regions = []
    pos = 0
    for clear, enc in subsamples:
        pos += clear
        if enc > 0:
            regions.append((pos, pos + enc))
        pos += enc
    return regions


def _parse_track(moov, t_off):
    """解析 trak -> (sizes, offsets, cns, aux_off, aux_sz, ns) 或 None。"""
    stbl_off, _ = _find_box(moov, "stbl", t_off + 8)

    stsz = _get_box(moov, "stsz", stbl_off)
    if stsz is None or len(stsz) < 12:
        return None
    ds = int.from_bytes(stsz[4:8], "big")
    ns = int.from_bytes(stsz[8:12], "big")
    sizes = []
    if ds == 0:
        for i in range(ns):
            if 16 + i * 4 > len(stsz):
                break
            sizes.append(int.from_bytes(stsz[12 + i * 4:16 + i * 4], "big"))
    else:
        sizes = [ds] * ns

    stco = _get_box(moov, "stco", stbl_off)
    if stco is None or len(stco) < 8:
        return None
    nc = int.from_bytes(stco[4:8], "big")
    offsets = []
    for i in range(nc):
        if 12 + i * 4 > len(stco):
            break
        offsets.append(int.from_bytes(stco[8 + i * 4:12 + i * 4], "big"))

    stsc = _get_box(moov, "stsc", stbl_off)
    if stsc is None or len(stsc) < 8:
        return None
    nsc = int.from_bytes(stsc[4:8], "big")
    entries = []
    for i in range(nsc):
        base = 8 + i * 12
        if base + 12 > len(stsc):
            break
        entries.append((int.from_bytes(stsc[base:base + 4], "big"),
                        int.from_bytes(stsc[base + 4:base + 8], "big"),
                        int.from_bytes(stsc[base + 8:base + 12], "big")))

    cns = [0] * nc
    for i in range(nsc):
        fc, spc = entries[i][0], entries[i][1]
        end = nc
        if i + 1 < nsc:
            end = entries[i + 1][0] - 1
        for c in range(fc - 1, min(end, nc)):
            cns[c] = spc

    saiz = _get_box(moov, "saiz", stbl_off)
    if saiz is None or len(saiz) < 9:
        return None
    da = saiz[4]
    na = int.from_bytes(saiz[5:9], "big")

    saio = _get_box(moov, "saio", stbl_off)
    if saio is None or len(saio) < 12:
        return None
    aux_off = int.from_bytes(saio[8:12], "big")
    # senc 盒实际大小优先（na*max(da,8) 只是兜底估算）
    senc_o, senc_sz = _find_box(moov, "senc", stbl_off)
    if senc_o >= 0 and senc_sz > 8:
        aux_sz = senc_sz - 8
    else:
        aux_sz = na * max(da, 8)

    return sizes, offsets, cns, aux_off, aux_sz, ns


def _iter_trak_offsets(moov):
    start = 0
    while True:
        off, sz = _find_box(moov, "trak", start)
        if off < 0:
            return
        yield off, sz
        start = off + sz


def _trak_handler(moov, t_off):
    """mdia->hdlr 的 handler_type（vide / soun / 其它）。"""
    h_off, _ = _find_box(moov, "hdlr", t_off)
    if h_off < 0:
        return b""
    if h_off + 20 <= len(moov):
        return bytes(moov[h_off + 16:h_off + 20])
    return b""


def _track_enc_config(moov, t_off, t_sz):
    """读取 trak 加密配置 -> (iv_len, constant_iv, use_subsample, entry_size)。"""
    iv_len, constant_iv, use_subsample, entry_size = 8, b"", False, 6
    o, _s = _find_box(moov, "tenc", t_off)
    if o >= 0 and o + 30 <= len(moov):
        version = moov[o + 8]
        flags = int.from_bytes(moov[o + 9:o + 12], "big")
        iv_len = moov[o + 13]
        if version >= 1:
            civ_len = moov[o + 30]
            if civ_len:
                constant_iv = bytes(moov[o + 31:o + 31 + civ_len])
        use_subsample = bool(flags & 0x01)
        if flags & 0x02:
            entry_size = 8
    if iv_len not in (0, 8, 16):
        iv_len = 8
    return iv_len, constant_iv, use_subsample, entry_size


def _track_saiz_da(moov, t_off, iv_len):
    o, _s = _find_box(moov, "saiz", t_off)
    if o >= 0 and o + 17 <= len(moov):
        return moov[o + 12]
    return iv_len


def _parse_sample_infos(aux_data, na, iv_len, constant_iv, use_subsample,
                        entry_size, da):
    """按 CENC 规范解析 senc 每样本辅助信息 -> [(iv, subsamples_or_None)]。
    该站 muxer 的 tenc 把 default_IV_size 写成 0，但 saiz(da>0) 实际每样本
    存了 IV，此时按 da 取 IV 宽度。"""
    if iv_len == 0 and da and da > 0:
        iv_len = da if not use_subsample else 8
    infos = []
    p = 0
    n = len(aux_data)
    sub_bytes = (da - iv_len) if (use_subsample and da and da > iv_len) else 0
    for _ in range(na):
        if iv_len == 0:
            iv = constant_iv
        else:
            iv = bytes(aux_data[p:p + iv_len])
            p += iv_len
        subs = None
        if sub_bytes and sub_bytes % entry_size == 0:
            cnt = sub_bytes // entry_size
            subs = []
            for _e in range(cnt):
                if p + entry_size > n:
                    break
                if entry_size == 6:
                    clear = int.from_bytes(aux_data[p:p + 2], "big")
                    enc = int.from_bytes(aux_data[p + 2:p + 6], "big")
                else:
                    clear = int.from_bytes(aux_data[p:p + 4], "big")
                    enc = int.from_bytes(aux_data[p + 4:p + 8], "big")
                subs.append((clear, enc))
                p += entry_size
        infos.append((iv, subs))
    return infos


def build_decrypt_map(data, total_size=None):
    """遍历所有 trak，生成 {sample_file_off: (size, iv, subsamples)}。
    data 只需包含完整 moov（流式代理可只传文件头）；total_size 为上游
    文件总长度（不传则取 len(data)）。整片解密时传完整文件即可。"""
    data = bytearray(data)
    if total_size is None:
        total_size = len(data)
    ftyp_end = int.from_bytes(data[0:4], "big")
    if ftyp_end + 8 >= len(data):
        raise ValueError("invalid MP4: ftyp too large")
    moov_size = int.from_bytes(data[ftyp_end:ftyp_end + 4], "big")
    if ftyp_end + 8 + moov_size > len(data):
        raise ValueError("invalid MP4: moov out of range")
    moov = data[ftyp_end + 8:ftyp_end + moov_size]
    moov_start = ftyp_end + 8

    dmap = {}
    stats = []
    for t_off, t_sz in _iter_trak_offsets(moov):
        handler = _trak_handler(moov, t_off)
        result = _parse_track(moov, t_off)
        if result is None:
            continue
        sizes, offsets, cns, aux_off, aux_sz, ns = result
        if ns == 0:
            continue
        # saio 偏移：优先按绝对文件偏移；越界时按 moov 内相对偏移兜底
        if aux_off + aux_sz <= len(data):
            aux_off_abs = aux_off
        elif moov_start + aux_off + aux_sz <= len(data):
            aux_off_abs = moov_start + aux_off
        else:
            continue
        if aux_off_abs + aux_sz > len(data):
            continue
        aux = bytes(data[aux_off_abs:aux_off_abs + aux_sz])

        iv_len, constant_iv, use_subsample, entry_size = _track_enc_config(moov, t_off, t_sz)
        da = _track_saiz_da(moov, t_off, iv_len)
        infos = _parse_sample_infos(aux, ns, iv_len, constant_iv,
                                    use_subsample, entry_size, da)
        si = 0
        for ci, off in enumerate(offsets):
            for _ in range(cns[ci]):
                if si >= ns:
                    break
                sz = sizes[si]
                if off + sz > total_size:
                    break
                iv, subs = infos[si] if si < len(infos) else (b"", None)
                dmap[off] = (sz, iv, subs)
                off += sz
                si += 1
        stats.append((handler, ns, iv_len, use_subsample))
    return dmap, stats


def _cenc_decrypt_with_map(data, dmap, content_key):
    """按 build_decrypt_map 的结果原地解密 data。"""
    for off in sorted(dmap.keys()):
        sz, iv, subs = dmap[off]
        base_ctr = _iv_to_ctr(iv, len(iv))
        for r0, r1 in _enc_regions(subs, sz):
            _ctr_decrypt_region(data, off + r0, r1 - r0, content_key, base_ctr, r0)


def _replace_sinf(data):
    """sinf -> free + 零填充（播放器不再尝试解密封装）。"""
    i = 0
    while i < len(data) - 4:
        if data[i:i + 4] == b"sinf":
            if i >= 4:
                sz = int.from_bytes(data[i - 4:i], "big")
                if 0 < sz < 50000:
                    data[i:i + 4] = b"free"
                    end = min(i - 4 + sz, len(data))
                    for j in range(i + 4, end):
                        data[j] = 0
                    i = end
                    continue
        i += 1


def _frma_of_entry(moov, box_start, box_end):
    """样本条目盒（enca/encv）内 sinf->frma 声明的原始格式 4CC；无则 None。"""
    seg = bytes(moov[box_start:box_end])
    si = seg.find(b"sinf")
    if si < 0:
        return None
    fi = seg.find(b"frma", si)
    if fi < 0 or fi + 8 > len(seg):
        return None
    return seg[fi + 4:fi + 8]


def _patch_moov_boxes(moov):
    """moov(bytearray) 原地改写：
    1) enca/encv 样本条目四俗称 -> 该条目 sinf/frma 声明的原始格式
       （mp4a / Opus / ec-3 / ac-3 / fLaC / avc1 / hvc1 / av01 ...）；
    2) sinf 盒 -> free + 零填充。
    frma 缺失时按盒内 config 盒回退：avcC->avc1 / hvcC->hvc1 / av1C->av01 /
    enca(含 esds)->mp4a；仍无法判定则保持 enca/encv 原样。
    注意：盒位置并非 4 对齐（样本条目大小任意），必须逐字节扫描，
    并以「盒大小合理 + 盒内含 frma/config 证据」排除密文里的随机命中。
    """
    n = len(moov)
    i = 0
    while i < n - 8:
        if moov[i:i + 4] in (b"enca", b"encv") and i >= 4:
            box_size = int.from_bytes(moov[i - 4:i], "big")
            if 8 <= box_size <= 10 * 1024 * 1024 and i - 4 + box_size <= n:
                box_start, box_end = i - 4, i - 4 + box_size
                seg = bytes(moov[box_start:box_end])
                fmt = _frma_of_entry(moov, box_start, box_end)
                if fmt is None:
                    if b"avcC" in seg:
                        fmt = b"avc1"
                    elif b"hvcC" in seg:
                        fmt = b"hvc1"
                    elif b"av1C" in seg:
                        fmt = b"av01"
                    elif moov[i:i + 4] == b"enca" and b"esds" in seg:
                        fmt = b"mp4a"
                if fmt and len(fmt) == 4 and fmt not in (b"enca", b"encv"):
                    moov[i:i + 4] = fmt
        i += 1
    _replace_sinf(moov)


def _detect_video_codec(buf):
    """仅按盒内 codec config 推断视频 fourcc（avcC/hvcC/av1C）。"""
    if b"avcC" in buf:
        return b"avc1"
    if b"hvcC" in buf:
        return b"hvc1"
    if b"av1C" in buf:
        return b"av01"
    return b"hvc1"


def decrypt_mp4_cenc(data, content_key):
    """整片 CENC 解密 + fourcc/sinf 改写，返回 bytes。"""
    data = bytearray(data)
    ftyp_end = int.from_bytes(data[0:4], "big")
    if ftyp_end + 8 >= len(data):
        raise ValueError("invalid MP4: ftyp too large")
    moov_size = int.from_bytes(data[ftyp_end:ftyp_end + 4], "big")
    if ftyp_end + 8 + moov_size > len(data):
        raise ValueError("invalid MP4: moov out of range")
    moov_start = ftyp_end + 8
    moov_end = ftyp_end + moov_size
    moov = data[moov_start:moov_end]

    dmap, stats = build_decrypt_map(data)
    _cenc_decrypt_with_map(data, dmap, content_key)

    # fourcc / sinf 改写只作用于 moov，避免误伤 mdat 密文
    _patch_moov_boxes(moov)
    data[moov_start:moov_end] = moov
    return bytes(data)


def stream_cenc_decrypt_chunk(chunk, chunk_start, decrypt_map, content_key):
    """流式分片解密：只处理与本分片重叠的样本区段。
    decrypt_map: {sample_off: (size, iv, subsamples)}。"""
    chunk = bytearray(chunk)
    chunk_end = chunk_start + len(chunk)

    for sample_off in list(decrypt_map.keys()):
        entry = decrypt_map[sample_off]
        sample_sz = entry[0]
        iv = entry[1]
        subsamples = entry[2] if len(entry) > 2 else None
        sample_end = sample_off + sample_sz

        if sample_off >= chunk_end or sample_end <= chunk_start:
            continue

        base_ctr = _iv_to_ctr(iv, len(iv))
        for r0, r1 in _enc_regions(subsamples, sample_sz):
            reg_start = sample_off + r0
            reg_end = sample_off + r1
            overlap_start = max(reg_start, chunk_start)
            overlap_end = min(reg_end, chunk_end)
            if overlap_start >= overlap_end:
                continue
            offset_in_sample = overlap_start - sample_off
            _ctr_decrypt_region(chunk, overlap_start - chunk_start,
                                overlap_end - overlap_start, content_key,
                                base_ctr, offset_in_sample)
    return bytes(chunk)


# ===========================================================================
# 小说/漫画内容 URL 与正文清洗（content.rs / content_util.rs / manga.rs）
# ===========================================================================
CONTENT_FULL_URL = "https://reading.snssdk.com/reading/reader/full/v/"
CONTENT_BATCH_URL = "https://api5-normal-sinfonlineb.fqnovel.com/reading/reader/batch_full/v"

_CONTENT_STRIP_RES = [
    _re.compile(r'<p class="pictureDesc" group-id="\d+" idx="\d+">'),
    _re.compile(r"</body>|</html>|</div>"),
    _re.compile(r'<p class="picture" group-id="\d+">'),
    _re.compile(r'<div data-fanqie-type="image" source="user">'),
    _re.compile(r"(?s)<head>.*</h1>"),
    _re.compile(r"(?s)<!DOCTYPE.*<html>"),
    _re.compile(r"(?s)<\?xml.*\?>"),
    _re.compile(r'<p idx="\d+">'),
    _re.compile(r"(?s)<header>.*</header>"),
    _re.compile(r"<article>|</article>"),
    _re.compile(r"<footer>|</footer>"),
    _re.compile(r"(?s)<tt_keyword.*keyword_ad>"),
    _re.compile(r"<p>"),
]


def build_content_url(item_id, api_type="full"):
    esc = go_query_escape(item_id)
    if api_type == "full":
        return ("%s?aid=1967&app_name=novelapp&channel=0&device_platform=android"
                "&device_id={device_id}&device_type=Honor10&item_id=%s"
                "&os_version=0&version_code=66.9" % (CONTENT_FULL_URL, esc))
    return ("%s?aid=1967&app_name=novelapp&channel=0&device_platform=android"
            "&device_id={device_id}&device_type=Honor10&os_version=0"
            "&version_code=66.9&book_id=0&item_ids=%s&novel_text_type=1"
            "&req_type=1" % (CONTENT_BATCH_URL, esc))


def process_full_content(content):
    """br/p -> 换行、去标签、去广告壳、合并空行（content_util.rs）。"""
    c = _re.sub(r"(?i)<\s*br\s*/?>", "\n", content)
    c = _re.sub(r"(?i)<\s*p[^>]*>", "\n", c)
    c = _re.sub(r"(?i)</\s*p\s*>", "\n", c)
    c = _re.sub(r"<[^>]*>", "", c)
    for rx in _CONTENT_STRIP_RES:
        c = rx.sub("", c)
    c = c.replace("&amp;x", "&x")
    c = _re.sub(r"\n{2,}", "\n", c)
    return c.strip()


def manga_origin_image_url(uri):
    if not uri:
        return ""
    if uri.startswith("http://") or uri.startswith("https://"):
        return uri
    return "https://p3-novel.byteimg.com/origin/%s" % uri.lstrip("/")


def _html_unescape(s):
    """Go html.UnescapeString 的常用子集（命名 + 十进制 + 十六进制实体）。"""
    if "&" not in s:
        return s
    return _html_mod.unescape(s)


def extract_manga_material_urls(content):
    """新版漫画内容：materials(type=img) + skeleton.data[].elementInfo 定序。"""
    raw = _html_unescape(content)
    start = raw.find("{")
    end = raw.rfind("}")
    if start < 0 or end <= start:
        return []
    try:
        payload = _json.loads(raw[start:end + 1])
    except Exception:
        return []
    materials = payload.get("materials") if isinstance(payload, dict) else None
    if not isinstance(materials, dict) or not materials:
        return []
    seen = set()
    urls = []

    def add(key):
        if not isinstance(key, str):
            return
        m = materials.get(key)
        if not isinstance(m, dict) or m.get("type") != "img":
            return
        data = m.get("data") if isinstance(m.get("data"), dict) else {}
        uri = data.get("web_uri") or data.get("encrypt_web_uri") or ""
        u = manga_origin_image_url(uri if isinstance(uri, str) else "")
        if not u or u in seen:
            return
        seen.add(u)
        urls.append(u)

    skeleton = payload.get("skeleton")
    items = skeleton.get("data") if isinstance(skeleton, dict) else None
    if isinstance(items, list):
        for it in items:
            if isinstance(it, dict):
                add(it.get("elementInfo"))
    if urls:
        return urls
    for key in sorted(materials.keys()):
        add(key)
    return urls


def parse_manga_pic_infos(content):
    """旧版漫画内容：{encrypt_key: hex32, picInfos: [{picUrl}]}。"""
    start = content.find("{")
    end = content.rfind("}")
    if start < 0 or end <= start:
        return "", []
    try:
        payload = _json.loads(content[start:end + 1])
    except Exception:
        return "", []
    if not isinstance(payload, dict):
        return "", []
    key = payload.get("encrypt_key")
    key = key if isinstance(key, str) else ""
    pics = payload.get("picInfos")
    out = []
    if isinstance(pics, list):
        for p in pics:
            if isinstance(p, dict) and isinstance(p.get("picUrl"), str) and p["picUrl"]:
                out.append(p["picUrl"])
    return key, out


def detect_image_format(data, url):
    path = _urlparse.urlsplit(url).path
    ext = path.rsplit(".", 1)[-1].lower() if "." in path.rsplit("/", 1)[-1] else ""
    if ext in ("jpg", "jpeg"):
        return "jpg"
    if ext in ("png", "gif", "webp"):
        return ext
    if len(data) >= 3 and data[0] == 0xff and data[1] == 0xd8 and data[2] == 0xff:
        return "jpg"
    if len(data) >= 4 and data[0] == 0x89 and data[1:4] == b"PNG":
        return "png"
    if len(data) >= 4 and data[:4] == b"GIF8":
        return "gif"
    if len(data) >= 12 and data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "webp"
    return "png"


class FqBox(object):
    """番茄系上游客户端（DeviceSigned 全链路）。"""

    def __init__(self, custom_device=None):
        self.store = DeviceStore()
        if custom_device:
            self.store.set_custom(custom_device)
        self.sign = SignManager()
        self.up = UpstreamClient(self.store, self.sign)

    # ---- 通用 ----
    def api_json(self, method, url, body=None, headers=None, timeout=15):
        raw = self.up.do_with_device(method, url, body, headers, timeout)
        return _json.loads(raw.decode("utf-8", "replace"))

    def unsigned_get(self, url, user_agent=FALLBACK_USER_AGENT, timeout=15):
        try:
            data, _ = self.up.do_resp("GET", url, None,
                                      [("User-Agent", user_agent)], True, timeout)
            return _json.loads(data.decode("utf-8", "replace"))
        except Exception:
            return None

    def unsigned_get_bytes(self, url, user_agent=UA_WINDOWS_BROWSER, timeout=20):
        try:
            data, _ = self.up.do_resp("GET", url, None,
                                      [("User-Agent", user_agent)], True, timeout)
            return data
        except Exception:
            return None

    # ---- 搜索（endpoints/search.rs）----
    READING_SEARCH_URL = ("https://api5-normal-sinfonlineb.fqnovel.com"
                          "/reading/bookapi/search/tab/v?")
    READING_SEARCH_SUFFIX = ("&tab_name=store&pad_column_cover=0&is_first_enter_search=false"
                             "&iid={install_id}&device_id={device_id}&ac=wifi"
                             "&channel=xiaomi_1967_64&aid=1967&app_name=novelapp"
                             "&version_code=65132&version_name=6.5.1.32&device_platform=android"
                             "&os=android&ssmix=a&device_type=FRD-AL10&device_brand=honor"
                             "&language=zh&os_api=28&os_version=9&manifest_version_code=65132"
                             "&resolution=1080%2A1920&dpi=480&update_version_code=65132"
                             "&pv_player=65132&gender=2&need_personal_recommend=1"
                             "&player_so_load=1&is_android_pad_screen=0&host_abi=arm64-v8a"
                             "&dragon_device_type=phone&rom_version=FRD-AL10%2B8.0.0.556%28C00%29"
                             "&compliance_status=0")
    FANQIE_SEARCH_URL = ("https://api.fanqiesdk.com/api/novel/channel/homepage/search/search/v1/?")
    FANQIE_SEARCH_SUFFIX = ("&enterfrom_aid=&enter_from=inner_search&app_name=news_article"
                            "&version_name=7.0.8&app_version=7.0.8&channel=tt_huawei2019_yz"
                            "&version_code=708&device_platform=android&parent_enterfrom=novel_list"
                            "&novel_host=&aid=13&scm_version=1.0.0.4112&device_type=25053RT47C"
                            "&device_brand=Redmi&language=zh&os_api=35&os_version=15"
                            "&openudid={openudid}&update_version_code=70899&plugin=0"
                            "&tma_jssdk_version=1.10.0.0&rom_version=miui__os2.0.209.0.volcnxm")

    def search_reading(self, query, offset="0", count="0", tab_type="1", passback=None):
        esc = go_query_escape
        if passback is None:
            passback = offset
        u = ("%sbookshelf_search_plan=4&offset=%s&user_is_login=1&bookstore_tab=2"
             "&passback=%s&query=%s&count=%s&search_source=1&clicked_content=search_history"
             "&use_lynx=false&use_correct=true&tab_type=%s%s" % (
                 self.READING_SEARCH_URL, esc(offset), esc(passback), esc(query),
                 esc(count), esc(tab_type), self.READING_SEARCH_SUFFIX))
        return self.api_json("GET", u, None, dragon_read_headers())

    def search_fanqie(self, query, offset="0"):
        u = "%sq=%s&offset=%s%s" % (self.FANQIE_SEARCH_URL,
                                    go_query_escape(query), go_query_escape(offset),
                                    self.FANQIE_SEARCH_SUFFIX)
        raw = self.up.do_with_device("GET", u, None,
                                     [("User-Agent", "com.ss.android.article.news/13400")])
        return _json.loads(strip_control_chars(raw).decode("utf-8", "replace"))

    # ---- 视频/短剧（endpoints/video.rs）----
    def fetch_shortplay_video_model(self, video_id):
        body = _json.dumps({
            "video_id": video_id,
            "content_type": 1004,
            "biz_param": {
                "detail_page_version": 0,
                "device_level": 3,
                "disable_digg_stat": False,
                "disable_video_relate_book": False,
                "from_video_id": "",
                "need_all_video_definition": True,
                "need_mp4_align": False,
                "source": 4,
                "use_os_player": False,
                "use_server_dns": False,
                "video_platform": 3,
            },
        }, separators=(",", ":")).encode("utf-8")
        return self.api_json("POST", SHORTPLAY_VIDEO_MODEL_URL, body, dragon_read_json_headers())

    def fetch_phoenix_video_model(self, video_id):
        body = _json.dumps({
            "biz_param": {
                "detail_page_version": 0,
                "device_level": 3,
                "disable_digg_stat": False,
                "need_all_video_definition": True,
                "need_mp4_align": False,
                "use_os_player": False,
                "use_server_dns": False,
                "video_platform": 1024,
            },
            "mixed_video_id_map": {"1004": [video_id]},
        }, separators=(",", ":")).encode("utf-8")
        return self.api_json("POST", phoenix_player_url(), body, phoenix_player_headers())

    def video_detail(self, series_id, video_id_type=1, source=5, video_platform=None):
        biz_param = {
            "device_level": 3,
            "need_all_video_definition": True,
            "need_mp4_align": False,
            "source": source,
            "use_os_player": False,
            "video_id_type": video_id_type,
        }
        if video_platform is not None:
            biz_param["video_platform"] = video_platform
        body = _json.dumps({"series_id": series_id, "biz_param": biz_param},
                           separators=(",", ":")).encode("utf-8")
        return self.api_json("POST", video_detail_url(), body, phoenix_player_headers())

    def pseries(self, pseries_id, offset="1", count="30", total="80", pseries_type="5"):
        body = _json.dumps({
            "biz_param": {
                "detail_page_version": 0,
                "device_level": 3,
                "disable_digg_stat": False,
                "need_all_video_definition": True,
                "need_mp4_align": False,
                "use_os_player": False,
                "use_server_dns": False,
                "video_platform": 1024,
                "pseries_type": pseries_type,
                "offset": offset,
                "count": count,
                "total": total,
                "from_category": "search",
                "category_name": "related",
                "mode": "range",
                "continue_play": 0,
            },
            "mixed_video_id_map": {"1004": [pseries_id]},
        }, separators=(",", ":")).encode("utf-8")
        return self.api_json("POST", phoenix_player_url(), body, phoenix_player_headers())

    def directory_reading(self, book_id):
        u = ("https://api5-normal-sinfonlineb.fqnovel.com/reading/bookapi/directory/all_items/v?"
             "book_type=0&item_data_list_md5=&catalog_data_md5=&book_id=%s"
             "&book_info_md5=&need_version=true&device_id={device_id}&ac=wifi"
             "&channel=xiaomi_1967_64&aid=1967&app_name=novelapp&version_code=65132"
             "&version_name=6.5.1.32&device_platform=android&os=android&ssmix=a"
             "&device_type=FRD-AL10&device_brand=honor&language=zh&os_api=28&os_version=9"
             "&manifest_version_code=65132&resolution=1080*1920&dpi=480"
             "&update_version_code=65132&pv_player=65132&=&need_personal_recommend=1"
             "&player_so_load=1&is_android_pad_screen=0&host_abi=arm64-v8a"
             "&dragon_device_type=phone&rom_version=FRD-AL10+8.0.0.556%%28C00%%29"
             "&compliance_status=0" % go_query_escape(book_id))
        return self.api_json("GET", u, None,
                             [("User-Agent", "Mozilla/5.0 (Linux; Android 13)")])

    # ---- 书城频道/推荐（endpoints/home.rs）----
    def bookmall_tab(self, tab_type="16", bottom_tab_type="7", client_req_type="3"):
        p = _reading724_params()
        p += [
            ("last_search_query_from_rec", "false"),
            ("ClickedContent", ""),
            ("client_template", "0"),
            ("last_tab_index", "0"),
            ("screen_width_px", "1281"),
            ("classic_tab_style", "v3"),
            ("tab_type", tab_type),
            ("first_use_category_select", "false"),
            ("last_session_video_tab_type", "0"),
            ("current_name", ""),
            ("disable_digg_stat", "false"),
            ("ecom_refresh_type", "0"),
            ("pad_column_cover", "0"),
            ("last_tab_type", "-1"),
            ("req_rank_category_id", "0"),
            ("video_tab_cold_start", "0"),
            ("offset", "0"),
            ("video_type_preferences_str", "[]"),
            ("auth_aweme", "false"),
            ("cold_start_is_double_gd", "false"),
            ("page_entry_time", "0"),
            ("cold_start_session", "1"),
            ("tab_index", "0"),
            ("lore_tab_style", "v5"),
            ("device_level", "3"),
            ("unlimited_short_series_change_type", "0"),
            ("book_id", "0"),
            ("ecom_impression_start_time", "0"),
            ("enable_search_box_collapse", "false"),
            ("landing_bottom_tab_type", "0"),
            ("bottom_tab_type", bottom_tab_type),
            ("top_tab_extra", ""),
            ("migration_top_tab_enable", "false"),
            ("auth_backward", "true"),
            ("pad_column_detail", "0"),
            ("after_genre_preference_popup", "0"),
            ("client_req_type", client_req_type),
            ("req_rank_algo", "101"),
            ("unlimited_short_series_next_offset", "0"),
            ("normal_session_cnt_in_day", "6"),
            ("cold_start_session_cnt_in_day", "2"),
            ("sys_mini_window", "1"),
            ("app_mini_window", "0"),
            ("har_status", "0"),
            ("cold_start_session_cnt_in_life", "2"),
            ("charging", "0"),
            ("normal_session_cnt_in_life", "6"),
            ("is_power_save_mode", "0"),
            ("app_dark_mode", "0"),
            ("screen_brightness", "36"),
            ("battery_pct", "10"),
            ("down_speed", "51430"),
            ("sys_dark_mode", "0"),
            ("font_scale", "100"),
            ("network_type", "4"),
            ("current_volume", "0"),
        ]
        url = build_upstream_url(HOST_FQNOVEL, "/reading/bookapi/bookmall/tab/v", p)
        return self.api_json("GET", url, None, dragon_read_headers())

    def series_feed(self, cell_id, tab_type="16", offset="0", timeout=None, **extra):
        p = _reading724_params()
        p += [
            ("cell_id", cell_id),
            ("last_search_query_from_rec", "false"),
            ("ClickedContent", ""),
            ("client_template", "2"),
            ("last_tab_index", "0"),
            ("screen_width_px", "1281"),
            ("classic_tab_style", "v3"),
            ("tab_type", tab_type),
            ("first_use_category_select", "false"),
            ("last_session_video_tab_type", "0"),
            ("current_name", ""),
            ("disable_digg_stat", "false"),
            ("ecom_refresh_type", "0"),
            ("pad_column_cover", "0"),
            ("last_tab_type", "0"),
            ("req_rank_category_id", "0"),
            ("video_tab_cold_start", "0"),
            ("offset", offset),
            ("video_type_preferences_str", "[]"),
            ("auth_aweme", "false"),
            ("cold_start_is_double_gd", "false"),
            ("page_entry_time", "0"),
            ("cold_start_session", "1"),
            ("tab_index", "0"),
            ("lore_tab_style", "v5"),
            ("device_level", "3"),
            ("unlimited_short_series_change_type", "0"),
            ("unlimited_selector_change_type", "2"),
            ("book_id", "0"),
            ("ecom_impression_start_time", "0"),
            ("enable_search_box_collapse", "false"),
            ("landing_bottom_tab_type", "0"),
            ("bottom_tab_type", "0"),
            ("top_tab_extra", ""),
            ("migration_top_tab_enable", "false"),
            ("auth_backward", "true"),
            ("pad_column_detail", "0"),
            ("after_genre_preference_popup", "0"),
            ("client_req_type", "2"),
            ("req_rank_algo", "101"),
            ("unlimited_short_series_next_offset", "0"),
            ("normal_session_cnt_in_day", "6"),
            ("cold_start_session_cnt_in_day", "2"),
            ("sys_mini_window", "1"),
            ("app_mini_window", "0"),
            ("har_status", "0"),
            ("cold_start_session_cnt_in_life", "2"),
            ("charging", "0"),
            ("normal_session_cnt_in_life", "6"),
            ("is_power_save_mode", "0"),
            ("app_dark_mode", "0"),
            ("screen_brightness", "36"),
            ("battery_pct", "10"),
            ("down_speed", "51430"),
            ("sys_dark_mode", "0"),
            ("font_scale", "100"),
            ("network_type", "4"),
            ("current_volume", "0"),
        ]
        for k, v in extra.items():
            if v is None:
                continue
            p = [(pk, pv) for pk, pv in p if pk != k]
            p.append((k, str(v)))
        url = build_upstream_url(HOST_FQNOVEL, "/reading/bookapi/bookmall/cell/change/v", p)
        if timeout is None:
            return self.api_json("GET", url, None, dragon_read_headers())
        return self.api_json("GET", url, None, dragon_read_headers(), timeout=timeout)

    # ---- 选流：短剧一集的全部清晰度 ----
    def resolve_video(self, video_id, stream=False, prefer_h265=True):
        """-> (url, key_hex, variants)。stream=True 时合并 phoenix 列表拿 1080P。
        prefer_h265=True 时把 fplay fallback_api 的 codec_type 改成 1（h265 档）——
        实测 3/4=bytevc1、0/1/2=h265；bytevc1 档解密后 frma 实为 hvc1 亦可播，
        但 h265 档位名更正、兼容性更好。"""
        raw = self.fetch_shortplay_video_model(video_id)
        bodies = [raw]
        if stream:
            try:
                bodies.append(self.fetch_phoenix_video_model(video_id))
            except Exception:
                pass

        scored = []
        best = ("notfound", None)
        fb_cache = {}

        def _fb(url):
            u = prefer_h265_fallback_url(url) if prefer_h265 else url
            if u not in fb_cache:
                fb_cache[u] = self.unsigned_get(u)
            return fb_cache[u]

        for body in bodies:
            resp = body if isinstance(body, dict) else None
            if resp is None:
                try:
                    resp = _json.loads(bytes(body).decode("utf-8", "replace"))
                except Exception:
                    continue
            data = _as_map(resp.get("data")) or {}
            for model in video_models(data):
                # 选流（resolve_video_source 语义）
                st, r = extract_shortplay_video_model_source(model)
                if best[0] == "notfound" and st != "notfound":
                    best = (st, r)
                if best[0] != "found" and video_model_encrypted(model):
                    fu = fallback_api_url(model)
                    if fu:
                        fb = _fb(fu)
                        if fb:
                            vi = _as_map(fb.get("video_info"))
                            dd = _as_map(vi.get("data")) if vi else None
                            if dd:
                                ks2 = dd.get("key_seed")
                                ks2b = audio_b64_decode(ks2) if isinstance(ks2, str) and ks2 else None
                                st2, r2 = extract_fallback_video_source(dd, ks2b)
                                if best[0] == "notfound" and st2 != "notfound":
                                    best = (st2, r2)
                # 清晰度列表（extract_stream_variants 语义：不做 encrypted 前置门）
                ks = model.get("key_seed")
                ks_b = audio_b64_decode(ks) if isinstance(ks, str) and ks else None
                scored.extend(variant_rows_scored(_as_map(model.get("video_list")), ks_b))
                fu = fallback_api_url(model)
                if fu:
                    fb = _fb(fu)
                    if fb:
                        vi = _as_map(fb.get("video_info"))
                        dd = _as_map(vi.get("data")) if vi else None
                        if dd:
                            ks2 = dd.get("key_seed")
                            ks2b = audio_b64_decode(ks2) if isinstance(ks2, str) and ks2 else None
                            scored.extend(variant_rows_scored(_as_map(dd.get("video_list")), ks2b))

        if best[0] == "notfound":
            st2, r2 = extract_video_url(raw)
            if st2 != "notfound":
                best = (st2, r2)
        variants = merge_variant_rows(scored)
        st, r = best
        if r is None and variants:
            r = (variants[0].get("url"),
                 bytes.fromhex(variants[0].get("key_hex") or ("00" * 16)))
        if r is None:
            return None, None, variants
        return r[0], r[1].hex(), variants

    # ---- 带设备的 JSON 请求（解密正文需要 secret_key）----
    def api_json_with_device(self, method, url, body=None, headers=None, timeout=15):
        last = None
        for _attempt in range(self.up.max_retries):
            dev = self.store.get()
            target = substitute_device(url, dev)
            try:
                raw = self.up.do_resp(method, target, body, headers, False, timeout)[0]
                return _json.loads(raw.decode("utf-8", "replace")), dev
            except DeviceFailed as e:
                last = e
                self.store.invalidate()
                _time.sleep(0.1)
                continue
        raise last if last else RuntimeError("device request failed")

    def api_json_signed(self, method, url, body=None, headers=None, timeout=15):
        raw = self.up.do_request(method, url, body, headers, timeout)
        return _json.loads(raw.decode("utf-8", "replace"))

    # ---- 小说/漫画正文（endpoints/content.rs）----
    def content_raw(self, item_id, api_type="full"):
        """-> (响应 JSON, 设备)。正文在 data.content（批量时 data[id].content）。"""
        u = build_content_url(item_id, api_type)
        return self.api_json_with_device("GET", u, None, dragon_read_headers())

    def content_full(self, item_id, api_type="full"):
        """-> (明文正文 bytes, book_id)。content.rs handle_single 语义。"""
        resp, dev = self.content_raw(item_id, api_type)
        data = _as_map(resp.get("data")) or {}
        content = data.get("content")
        book_id = ""
        nd = _as_map(data.get("novel_data"))
        if nd:
            book_id = nd.get("book_id") if isinstance(nd.get("book_id"), str) else ""
        if not isinstance(content, str) or not content:
            return b"", book_id
        try:
            return decrypt_upstream(content, dev.secret_key), book_id
        except Exception:
            return b"", book_id

    def book_detail_legacy(self, book_id):
        u = ("https://api5-normal-sinfonlineb.fqnovel.com/reading/bookapi/detail/v?"
             "book_id=%s&aid=1967&app_name=novelapp&channel=xiaomi_1967_64"
             "&version_code=65132&version_name=6.5.1.32&device_platform=android"
             "&os=android&device_id={device_id}&iid={install_id}&ssmix=a"
             "&device_type=FRD-AL10&device_brand=honor&language=zh&os_api=28"
             "&os_version=9&manifest_version_code=65132&resolution=1080*1920"
             "&dpi=480&update_version_code=65132&pv_player=65132&ac=wifi"
             "&host_abi=arm64-v8a&dragon_device_type=phone"
             "&rom_version=FRD-AL10%%2B8.0.0.556%%28C00%%29&compliance_status=0"
             % go_query_escape(book_id))
        return self.api_json("GET", u, None, dragon_read_headers())

    def novel_chapter(self, book_id, item_id):
        """-> 清洗后的章节正文文本。"""
        plain, _ = self.content_full(item_id, "full")
        if plain:
            text = plain.decode("utf-8", "replace")
            return process_full_content(text)
        return ""

    # ---- 漫画（endpoints/manga.rs）----
    def manga_chapter(self, item_id, api_type="full"):
        """-> {"images": [...], "encrypt_key": hex|"", "pic_urls": [...], "content": str}"""
        out = {"images": [], "encrypt_key": "", "pic_urls": [], "content": ""}
        plain, _ = self.content_full(item_id, api_type)
        if not plain:
            return out
        text = plain.decode("utf-8", "replace")
        out["content"] = text
        key, pics = parse_manga_pic_infos(text)
        if key and pics:
            out["encrypt_key"] = key
            out["pic_urls"] = pics
            return out
        urls = extract_manga_material_urls(text)
        if urls:
            out["images"] = urls
        return out

    def manga_image(self, url, key_hex):
        """下载并 AES-256-GCM 解密漫画图片 -> bytes。"""
        raw = self.unsigned_get_bytes(url, UA_WINDOWS_BROWSER)
        if raw is None or len(raw) <= 100:
            return None
        if key_hex:
            key = bytes.fromhex(key_hex)
            raw = aes256_gcm_decrypt(raw, key)
        return raw

    # ---- 听书（endpoints/audio.rs）----
    def audio_book_detail(self, book_id):
        p = _reading724_params()
        p.append(("version", "v3"))
        p.append(("book_id", book_id))
        url = build_upstream_url(HOST_FQNOVEL, "/reading/bookapi/audio/detail/", p)
        return self.api_json("GET", url, None, dragon_read_headers())

    def audio_chapter_info(self, book_id, chapter_id, tone_id="0"):
        p = _reading724_params()
        p.append(("book_id", book_id))
        p.append(("item_ids", chapter_id))
        p.append(("tone_id", tone_id))
        p.append(("req_type", "0"))
        p.append(("is_local_book", "false"))
        url = build_upstream_url(HOST_FQNOVEL, "/reading/reader/audio/playinfo/", p)
        return self.api_json("GET", url, None, dragon_read_headers())

    def audio_default_tone(self, book_id):
        """-> 默认 tone_id（data.tones 首个），取不到返回 "4"。"""
        try:
            d = self.audio_book_detail(book_id)
            data = _as_map(d.get("data")) or {}
            tones = data.get("tones")
            if isinstance(tones, str) and tones.strip():
                return tones.split(",")[0].strip() or "4"
            if isinstance(tones, list) and tones:
                return str(tones[0])
        except Exception:
            pass
        return "4"

    def audio_chapter_stream(self, book_id, chapter_id, tone_id=None):
        """-> (url, key_hex)。playinfo 的 main_url 已是明文直链。"""
        if not tone_id:
            tone_id = self.audio_default_tone(book_id)
        info = self.audio_chapter_info(book_id, chapter_id, tone_id)
        data = info.get("data")
        if not isinstance(data, list) or not data:
            return None, None
        row = _as_map(data[0]) or {}
        u = row.get("main_url") if isinstance(row.get("main_url"), str) else ""
        spade_a = row.get("encryption_key") if isinstance(row.get("encryption_key"), str) else ""
        if not spade_a:
            vm = _decode_video_model(row.get("video_model")) or {}
            vl = vm.get("video_list")
            entry = None
            if isinstance(vl, list) and vl:
                entry = _as_map(vl[0])
            elif isinstance(vl, dict) and vl:
                entry = _as_map(list(vl.values())[0])
            if entry:
                ei = _as_map(entry.get("encrypt_info")) or {}
                if not u:
                    u = entry.get("main_url") if isinstance(entry.get("main_url"), str) else ""
                if not spade_a:
                    spade_a = ei.get("spade_a") if isinstance(ei.get("spade_a"), str) else ""
        if not u or not spade_a:
            return None, None
        return u, derive_spade_content_key(spade_a).hex()

    def audio_play(self, book_id, item_ids, tone_id=0):
        p = [
            ("os", "android"), ("aid", "3040"), ("ssmix", "a"),
            ("manifest_version_code", "632"), ("dpi", "440"),
            ("device_brand", "Redmi"), ("language", "zh"), ("os_api", "35"),
            ("comment_tag_c", "5"), ("vip_state", "0"),
            ("host_abi", "arm64-v8a"), ("category_style", "1"),
            ("need_personal_recommend", "1"),
            ("rom_version", "miui_V816_OS3.0.1.0.VMRCNXM"),
        ]
        ids = [s.strip() for s in item_ids.split(",") if s.strip()]
        body = _json.dumps({
            "audio_type": 0, "bgm_used": 0, "book_id": book_id,
            "device_score": 0, "item_ids": ids, "multi_shift": False,
            "source": "default", "tone_id": int(tone_id),
            "user_select_start_para": 0, "user_select_start_para_off": 0,
        }, separators=(",", ":")).encode("utf-8")
        url = build_upstream_url("https://api5-sinfonlineb.novelfm.com",
                                 "/novelfm/playerapi/video_model/mget/v1", p)
        return self.api_json_signed("POST", url, body, dragon_read_json_headers())

    def audio_streams(self, book_id, item_ids, tone_id=0):
        """-> [(url, key_hex, display)]：audio_play 的 video_model 选流。"""
        v = self.audio_play(book_id, item_ids, tone_id)
        data = _as_map(v.get("data")) or {}
        rows = []
        for row in (data.get("video_model_datas") or []):
            if not isinstance(row, dict):
                continue
            model = _decode_video_model(row.get("video_model"))
            if model is None:
                continue
            ks = model.get("key_seed")
            ks_b = audio_b64_decode(ks) if isinstance(ks, str) and ks else None
            vl = _as_map(model.get("video_list")) or {}
            for info in vl.values():
                info = _as_map(info)
                if info is None:
                    continue
                r = decrypt_variant_entry(info, ks_b)
                if r is None:
                    continue
                rows.append({"url": r[0], "key_hex": r[1].hex(),
                             "encrypt": bool(_as_map(info.get("encrypt_info")))})
        seen = set()
        out = []
        for r in rows:
            if r["url"] in seen:
                continue
            seen.add(r["url"])
            out.append(r)
        return out


def extract_video_url(raw):
    """整棵响应的兜底：video_info_list_map / 明文 video_model。"""
    try:
        resp = _json.loads(raw.decode("utf-8", "replace")) if isinstance(raw, (bytes, bytearray)) else raw
    except Exception:
        return "notfound", None
    data = _as_map(resp.get("data")) or {}
    st, r = extract_video_info_list_map_url(data)
    if st != "notfound":
        return st, r
    for model in video_models(data):
        st, r = extract_video_model_url(model)
        if st != "notfound":
            return st, r
    return "notfound", None


def extract_fallback_video_source(data_root, key_seed):
    """fallback_api 响应里的 video_info.data.video_list 选流。"""
    video_list = _as_map(data_root.get("video_list"))
    if video_list is None:
        return "notfound", None
    return select_video_source(list(video_list.values()),
                               lambda info: decrypt_variant_entry(info, key_seed))


# ===========================================================================
# 以下为 TVBox Spider 层（本地解密代理 + 五类内容路由）
# ===========================================================================

# ===========================================================================
# Part 2 — 本地解密代理（ThreadingHTTPServer）
#   /stream?url=&key=  CENC 流式解密（整片下载解密缓存 + Range 快通道）
#   /play?vid=         解析 vid 后内联服务（带 5 分钟解析缓存）
#   /img?url=&key=     AES-256-GCM 图片解密（漫画/漫剧）
#   /health            健康检查
# ===========================================================================
import threading as _threading
from http.server import BaseHTTPRequestHandler as _BaseHTTPRequestHandler
from http.server import ThreadingHTTPServer as _ThreadingHTTPServer
import urllib.request as _urllib_request

_PROXY_CHUNK = 1024 * 1024          # 流式分块 1MB
_PROXY_HEAD_MIN = 1024 * 1024       # moov 探测起始 1MB
_PROXY_HEAD_MAX = 48 * 1024 * 1024  # moov 探测上限
_PROXY_MAP_TTL = 900                # decrypt_map 缓存 15 分钟
_PROXY_RESOLVE_TTL = 300            # vid 解析缓存 5 分钟
_PROXY_IMG_TTL = 3600               # 图片内存缓存 1 小时
_PROXY_IMG_MAX = 600                # 图片内存缓存条目上限
_PROXY_IMG_DISK_TTL = 24 * 3600     # 图片磁盘缓存 24 小时
_PROXY_IMG_PRELOAD = 4              # 图片预加载并发数
_PROXY_IMG_PRELOAD_MAX = 120        # 单话预加载张数上限
_CACHE_MAX_FILES = 40               # 视频磁盘缓存文件数上限
_CACHE_TTL = 6 * 3600               # 视频磁盘缓存 6 小时
_CACHE_IMG_MAX_FILES = 600          # 图片磁盘缓存文件数上限

# feed 分页：client_req_type 与步长（实测：短剧/漫剧只有 crt=1 才认 offset）
_FQ_FEED = {
    "short": {"crt": "1", "step": 6},
    "mdr":   {"crt": "1", "step": 12},
    "novel": {"crt": "2", "step": 20},
    "manga": {"crt": "2", "step": 20},
    "audio": {"crt": "2", "step": 20},
}
_FEED_TTL = 120                      # feed 原始项缓存 2 分钟（首页/分类页1 共用）
_HOME_TTL = 180                      # 首页缓存 3 分钟
_VAR_TTL = 300                       # 清晰度列表缓存 5 分钟
_SEARCH_PER_KIND = 15                # 搜索每类配额（防一类暴涨挤掉其他类）
_FEED_PAGE = 20                      # 对壳呈现的每页条数（兼容按 20/页 渲染的壳）
_FEED_BUF_MAX = 400                  # 视频类顺序缓冲上限（= 20 壳页），达到即停 walk
_FEED_STALE_MAX = 2                  # 连续几页零新增视为当前 selector 枯竭
_FEED_SEL_MIN_OFF = 120              # offset 走到该深度仍无新增才切 selector（兜底）
_FEED_SEL_MAX_SWITCH = 12            # 最多切换次数（防无效源刷屏）
_FEED_ENSURE_BUDGET = 15.0           # 深翻页同步补拉预算（秒）；deadline 下沉到
                                     # _feed_raw，单次请求超时随剩余预算收缩，
                                     # 最坏页等待 ≈ 预算+3s（旧行为 3 设备重试×15s）
_FEED_ENSURE_FIRST_BUDGET = 8.0      # 首屏预算（秒）：干净网络下足够凑满 20 条；
                                     # 慢/限流时按实际条数先出货（宁可短页不空白），
                                     # 余量由 walker 后台补满，下拉刷新即满页
_TABCELL_TTL = 6 * 3600              # tab cell_id 磁盘缓存 6 小时（跨进程复用）
# 短剧 feed 的内容源（selector）；漫剧上游不提供 selector，深度即推荐池大小
_FQ_SELECTORS = ["videoseries_hot_v2", "firstonlinetime_new", "cate_757",
                 "cate_1051", "cate_1", "cate_739", "cate_29", "cate_1207",
                 "cate_760", "cate_1021"]


def _proxy_cache_dir():
    try:
        import tempfile as _tf
        d = _os.path.join(_tf.gettempdir(), "fqtv_cache")
        try:
            _os.makedirs(d, exist_ok=True)
        except Exception:
            pass
        if _os.path.isdir(d):
            return d
    except Exception:
        pass
    return ""


_tabcell_lock = _threading.Lock()


def _tabcell_cache_path():
    """tab cell_id 磁盘缓存路径（与设备缓存同目录，跨进程复用）。"""
    base = ""
    try:
        base = _os.path.dirname(_os.path.abspath(_device_cache_path()))
    except Exception:
        base = ""
    if not base:
        try:
            import tempfile as _tf
            base = _tf.gettempdir()
        except Exception:
            base = "."
    return _os.path.join(base, "fqtv_tabcells.json")


def _tabcell_save(kind, cid):
    """落盘一个 kind 的 cell_id（读-改-写 + 原子替换，5 类并行首页安全）。"""
    try:
        with _tabcell_lock:
            p = _tabcell_cache_path()
            data = {}
            try:
                with open(p, "r", encoding="utf-8") as f:
                    data = _json.load(f)
                if not isinstance(data, dict):
                    data = {}
            except Exception:
                data = {}
            data[kind] = [cid, _time.time()]
            tmp = p + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                _json.dump(data, f)
            _os.replace(tmp, p)
    except Exception:
        pass


def _http_range(url, start, end, headers=None, timeout=30):
    """Range GET -> (status, data, total_or_None)。上游忽略 Range 时 status=200。"""
    h = {"Range": "bytes=%d-%d" % (start, end), "User-Agent": UA_WINDOWS_BROWSER}
    if headers:
        h.update(headers)
    req = _urllib_request.Request(url, headers=h)
    with _urllib_request.urlopen(req, timeout=timeout) as resp:
        status = resp.status if hasattr(resp, "status") else resp.getcode()
        data = resp.read()
        total = None
        cr = resp.headers.get("Content-Range")
        if cr and "/" in cr:
            tail = cr.rsplit("/", 1)[1].strip()
            if tail.isdigit():
                total = int(tail)
        if total is None:
            cl = resp.headers.get("Content-Length")
            if cl and cl.isdigit():
                total = int(cl)
        return status, data, total


def _http_get_full(url, headers=None, timeout=60):
    h = {"User-Agent": UA_WINDOWS_BROWSER}
    if headers:
        h.update(headers)
    req = _urllib_request.Request(url, headers=h)
    with _urllib_request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def _moov_range(head):
    """-> (moov_start, moov_end)；解析失败返回 None。"""
    try:
        if len(head) < 16:
            return None
        ftyp_end = int.from_bytes(head[0:4], "big")
        if ftyp_end + 8 > len(head):
            return None
        moov_size = int.from_bytes(head[ftyp_end:ftyp_end + 4], "big")
        if ftyp_end + 8 + moov_size > len(head):
            return None
        return (ftyp_end + 8, ftyp_end + moov_size)
    except Exception:
        return None


def _patch_moov_bytes(buf, moov_start, moov_end):
    """把缓冲区里 [moov_start, moov_end) 的 enca/encv/sinf 改写成明文四俗称。"""
    if moov_start is None:
        return buf
    buf = bytearray(buf)
    ms = max(0, moov_start)
    me = min(len(buf), moov_end)
    if me - ms < 16:
        return bytes(buf)
    moov = bytearray(buf[ms:me])
    _patch_moov_boxes(moov)
    buf[ms:me] = moov
    return bytes(buf)


def _patch_moov_in_file(path, moov_start, moov_end):
    if moov_start is None or not path:
        return
    try:
        with open(path, "r+b") as f:
            f.seek(moov_start)
            moov = bytearray(f.read(moov_end - moov_start))
            if len(moov) < 16:
                return
            _patch_moov_boxes(moov)
            f.seek(moov_start)
            f.write(moov)
    except Exception:
        pass


_PROXY_IMG_MIME = {"jpg": "image/jpeg", "jpeg": "image/jpeg", "png": "image/png",
                   "gif": "image/gif", "webp": "image/webp", "bmp": "image/bmp"}


def _img_mime(ctype):
    return _PROXY_IMG_MIME.get(str(ctype or "").lower(), "image/jpeg")


class _FqProxy(object):
    """本地解密代理。box（FqBox 实例）由 Spider.init 注入，供 /play 解析用。"""

    def __init__(self):
        self.server = None
        self.port = 0
        self.box = None
        self._started = False
        self._lock = _threading.Lock()
        self._maps = {}      # url -> (dmap, moov_range, ts)
        self._resolves = {}  # vid -> (url, key_hex, variants, ts)
        self._imgs = {}      # (url, key) -> (bytes, ctype, ts)
        self._img_locks = {}
        self._preload_seen = set()
        self._dl_locks = {}
        self._var_locks = {}

    # ---------------- 生命周期 ----------------
    def start(self):
        if self._started:
            return True
        proxy = self

        class _Handler(_BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, fmt, *args):
                pass

            def _send(self, code, body=b"", ctype="application/octet-stream", extra=None):
                try:
                    self.send_response(code)
                    self.send_header("Content-Type", ctype)
                    self.send_header("Content-Length", str(len(body)))
                    self.send_header("Accept-Ranges", "bytes")
                    self.send_header("Access-Control-Allow-Origin", "*")
                    if extra:
                        for k, v in extra.items():
                            self.send_header(k, v)
                    self.end_headers()
                    if self.command != "HEAD" and body:
                        self.wfile.write(body)
                except Exception:
                    pass

            def _json(self, code, obj):
                self._send(code, _json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                           "application/json")

            def do_GET(self):
                try:
                    parsed = _urlparse.urlparse(self.path)
                    params = {}
                    for k, v in _urlparse.parse_qs(parsed.query).items():
                        params[k] = v[0] if v else ""
                    path = parsed.path
                    if path == "/health":
                        self._json(200, {"ok": True, "port": proxy.port})
                    elif path == "/stream":
                        proxy.serve_stream(self, params.get("url", ""), params.get("key", ""))
                    elif path == "/play":
                        proxy.serve_play(self, params.get("vid", ""),
                                         params.get("q", ""))
                    elif path == "/img":
                        proxy.serve_image(self, params.get("url", ""), params.get("key", ""))
                    else:
                        self._send(404, b"not found", "text/plain")
                except Exception as e:
                    try:
                        self._json(500, {"error": "%s" % e})
                    except Exception:
                        pass

            def do_HEAD(self):
                self.do_GET()

        try:
            self.server = _ThreadingHTTPServer(("127.0.0.1", 0), _Handler)
            self.server.daemon_threads = True
            t = _threading.Thread(target=self.server.serve_forever,
                                  kwargs={"poll_interval": 0.5})
            t.daemon = True
            t.start()
            self.port = self.server.server_address[1]
            self._started = True
            return True
        except Exception:
            self._started = False
            return False

    def base(self):
        return "http://127.0.0.1:%d" % self.port

    def stream_url(self, url, key_hex=""):
        return "%s/stream?url=%s&key=%s" % (
            self.base(), _urlparse.quote(url, safe=""), key_hex or "")

    def play_url(self, vid, q=""):
        q = _urlparse.quote(str(q or ""), safe="")
        if q:
            return "%s/play?vid=%s&q=%s" % (
                self.base(), _urlparse.quote(str(vid), safe=""), q)
        return "%s/play?vid=%s" % (self.base(), _urlparse.quote(str(vid), safe=""))

    def img_url(self, url, key_hex):
        return "%s/img?url=%s&key=%s" % (
            self.base(), _urlparse.quote(url, safe=""), key_hex or "")

    # ---------------- decrypt_map ----------------
    def get_map(self, url):
        """-> (dmap, moov_range)。带 TTL 缓存。"""
        with self._lock:
            ent = self._maps.get(url)
            if ent and _time.time() - ent[2] < _PROXY_MAP_TTL:
                return ent[0], ent[1]
        dmap, moov = {}, None
        size = _PROXY_HEAD_MIN
        while size <= _PROXY_HEAD_MAX:
            try:
                _st, head, total = _http_range(url, 0, size - 1)
            except Exception:
                break
            if _st == 200:
                head, total = head, len(head)
            if len(head) < 16:
                break
            moov = _moov_range(head)
            try:
                dmap, _stats = build_decrypt_map(head, total or len(head))
            except Exception:
                dmap = {}
            if dmap:
                break
            if moov is not None and b"senc" not in head:
                break  # moov 完整且无 senc -> 明文文件
            if len(head) < size:
                break  # 上游已给全部
            size *= 2
        with self._lock:
            self._maps[url] = (dmap, moov, _time.time())
        return dmap, moov

    # ---------------- /stream ----------------
    def serve_stream(self, handler, url, key_hex):
        if not url:
            handler._send(400, b"missing url", "text/plain")
            return
        key = b""
        if key_hex:
            try:
                key = bytes.fromhex(key_hex)
            except Exception:
                key = b""

        dmap, moov = ({}, None)
        if key:
            try:
                dmap, moov = self.get_map(url)
            except Exception:
                dmap, moov = {}, None

        rng = handler.headers.get("Range") or ""
        m = _re.match(r"bytes=(\d*)-(\d*)", rng.strip())
        is_full = (not m) or (m.group(1) in ("", "0") and not m.group(2))

        if not key:
            # 明文：直接透传（带 Range）
            self._serve_plain(handler, url, rng)
            return

        # 密文：整片请求 -> 下载解密缓存后按 Range 服务；部分 Range -> CDN 快通道
        cache_path = self._cache_path(url)
        if is_full and cache_path and _os.path.isfile(cache_path):
            self._serve_file(handler, cache_path, rng)
            return

        if is_full:
            try:
                st, _d, total = _http_range(url, 0, 0)
            except Exception:
                st, total = 0, 0
            if total and cache_path:
                lock = self._dl_lock(url)
                if lock.acquire(blocking=False):
                    try:
                        if _os.path.isfile(cache_path):
                            self._serve_file(handler, cache_path, rng)
                            return
                        self._download_decrypt(handler, url, key, dmap, moov,
                                               cache_path, total, rng)
                        return
                    finally:
                        lock.release()
                else:
                    with lock:
                        pass
                    if _os.path.isfile(cache_path):
                        self._serve_file(handler, cache_path, rng)
                        return
            # 拿不到总长或不允许落盘：退化成快通道
            self._serve_range_fast(handler, url, key, dmap, rng)
            return

        self._serve_range_fast(handler, url, key, dmap, rng)

    def _serve_plain(self, handler, url, rng):
        try:
            st, _d, total = _http_range(url, 0, 0)
        except Exception:
            st, total = 0, 0
        start, end = 0, (total - 1) if total else 0
        m = _re.match(r"bytes=(\d*)-(\d*)", (rng or "").strip())
        partial = bool(m)
        if m:
            if m.group(1):
                start = int(m.group(1))
            if m.group(2):
                end = int(m.group(2))
            elif m.group(1):
                end = (total - 1) if total else start
        if total:
            end = min(end, total - 1)
            if start > end:
                handler._send(416, b"range not satisfiable", "text/plain")
                return
        length = end - start + 1
        extra = {}
        if partial:
            extra["Content-Range"] = "bytes %d-%d/%s" % (start, end, total or "*")
        handler.send_response(206 if partial else 200)
        handler.send_header("Content-Type", "video/mp4")
        handler.send_header("Content-Length", str(length))
        handler.send_header("Accept-Ranges", "bytes")
        for k, v in extra.items():
            handler.send_header(k, v)
        handler.end_headers()
        pos = start
        while pos <= end:
            n = min(_PROXY_CHUNK, end - pos + 1)
            try:
                st, raw, _t = _http_range(url, pos, pos + n - 1)
            except Exception:
                break
            if st == 200 and pos == 0 and not partial:
                raw = raw[:length]
            if not raw:
                break
            try:
                handler.wfile.write(raw)
            except Exception:
                break
            pos += len(raw)

    def _serve_range_fast(self, handler, url, key, dmap, rng):
        """部分 Range 快通道：只取请求区间解密，moov 保持原样（探测/拖动用）。"""
        try:
            st, _d, total = _http_range(url, 0, 0)
        except Exception:
            st, total = 0, 0
        start, end = 0, (total - 1) if total else 0
        m = _re.match(r"bytes=(\d*)-(\d*)", (rng or "").strip())
        partial = bool(m)
        if m:
            if m.group(1):
                start = int(m.group(1))
            if m.group(2):
                end = int(m.group(2))
            elif m.group(1):
                end = (total - 1) if total else start
        if total:
            end = min(end, total - 1)
            if start > end:
                handler._send(416, b"range not satisfiable", "text/plain")
                return
        length = end - start + 1
        extra = {}
        if partial:
            extra["Content-Range"] = "bytes %d-%d/%s" % (start, end, total or "*")
        handler.send_response(206 if partial else 200)
        handler.send_header("Content-Type", "video/mp4")
        handler.send_header("Content-Length", str(length))
        handler.send_header("Accept-Ranges", "bytes")
        for k, v in extra.items():
            handler.send_header(k, v)
        handler.end_headers()
        pos = start
        while pos <= end:
            n = min(_PROXY_CHUNK, end - pos + 1)
            try:
                st, raw, _t = _http_range(url, pos, pos + n - 1)
            except Exception:
                break
            if st == 200:
                seg = raw[pos:pos + n]
                if key and dmap and seg:
                    seg = stream_cenc_decrypt_chunk(seg, pos, dmap, key)
                if seg:
                    try:
                        handler.wfile.write(seg)
                    except Exception:
                        break
                pos += n
                continue
            if key and dmap and raw:
                raw = stream_cenc_decrypt_chunk(raw, pos, dmap, key)
            if not raw:
                break
            try:
                handler.wfile.write(raw)
            except Exception:
                break
            pos += len(raw)

    def _download_decrypt(self, handler, url, key, dmap, moov, path, total, rng):
        """整片下载+流式解密，边写缓存边响应；moov 在首块内打好补丁。"""
        handler.send_response(206 if rng else 200)
        handler.send_header("Content-Type", "video/mp4")
        handler.send_header("Content-Length", str(total))
        handler.send_header("Accept-Ranges", "bytes")
        if rng:
            handler.send_header("Content-Range", "bytes 0-%d/%d" % (total - 1, total))
        handler.end_headers()
        try:
            f = open(path, "wb")
        except Exception:
            f = None
        pos = 0
        first = True
        try:
            while pos < total:
                n = min(_PROXY_CHUNK, total - pos)
                try:
                    st, raw, _t = _http_range(url, pos, pos + n - 1)
                except Exception:
                    break
                if st == 200 and pos > 0:
                    break
                if not raw:
                    break
                if key and dmap:
                    raw = stream_cenc_decrypt_chunk(raw, pos, dmap, key)
                if first and key and dmap and moov:
                    raw = _patch_moov_bytes(raw, moov[0] - pos, moov[1] - pos)
                    first = False
                if f:
                    f.write(raw)
                handler.wfile.write(raw)
                pos += len(raw)
        except Exception:
            pass
        finally:
            if f:
                try:
                    f.close()
                except Exception:
                    pass
        if f and moov and _os.path.isfile(path) and _os.path.getsize(path) >= total:
            _patch_moov_in_file(path, moov[0], moov[1])
        self._cleanup_cache()

    def _serve_file(self, handler, path, rng):
        try:
            size = _os.path.getsize(path)
        except Exception:
            handler._send(404, b"cache miss", "text/plain")
            return
        start, end = 0, size - 1
        m = _re.match(r"bytes=(\d*)-(\d*)", (rng or "").strip())
        partial = bool(m)
        if m:
            if m.group(1):
                start = int(m.group(1))
            if m.group(2):
                end = int(m.group(2))
            elif m.group(1):
                end = size - 1
        end = min(end, size - 1)
        if start > end or start >= size:
            handler._send(416, b"range not satisfiable", "text/plain")
            return
        length = end - start + 1
        extra = {}
        if partial:
            extra["Content-Range"] = "bytes %d-%d/%d" % (start, end, size)
        handler.send_response(206 if partial else 200)
        handler.send_header("Content-Type", "video/mp4")
        handler.send_header("Content-Length", str(length))
        handler.send_header("Accept-Ranges", "bytes")
        for k, v in extra.items():
            handler.send_header(k, v)
        handler.end_headers()
        try:
            with open(path, "rb") as f:
                f.seek(start)
                remaining = length
                while remaining > 0:
                    chunk = f.read(min(65536, remaining))
                    if not chunk:
                        break
                    handler.wfile.write(chunk)
                    remaining -= len(chunk)
        except Exception:
            pass

    # ---------------- /play ----------------
    def serve_play(self, handler, vid, q=""):
        vid = str(vid or "").strip()
        if not vid:
            handler._send(400, b"missing vid", "text/plain")
            return
        url, key_hex = self._resolve(vid, q)
        if not url:
            handler._send(502, b"resolve failed", "text/plain")
            return
        self.serve_stream(handler, url, key_hex or "")

    def _resolve(self, vid, q=""):
        """-> (url, key_hex)。q 为清晰度名（如 1080P/720P）；空或找不到时取最高档。"""
        with self._lock:
            ent = self._resolves.get(vid)
            if ent and _time.time() - ent[3] < _PROXY_RESOLVE_TTL:
                url, key_hex, variants, _ts = ent
                if q:
                    for v in variants or []:
                        if v.get("name") == q and v.get("url"):
                            return v["url"], v.get("key_hex") or ""
                return url, key_hex
        url, key_hex, variants = "", "", []
        try:
            if self.box is not None:
                url, key_hex, variants = self.box.resolve_video(vid, stream=True)
        except Exception:
            url, key_hex, variants = "", "", []
        variants = [v for v in (variants or []) if isinstance(v, dict) and v.get("url")]
        if not url and variants:
            v0 = variants[0]
            url, key_hex = v0["url"], v0.get("key_hex") or ""
        with self._lock:
            self._resolves[vid] = (url or "", key_hex or "", variants, _time.time())
        if q:
            for v in variants:
                if v.get("name") == q and v.get("url"):
                    return v["url"], v.get("key_hex") or ""
        return url or "", key_hex or ""

    # ---------------- /img ----------------
    def _img_disk_path(self, url, key_hex):
        d = _proxy_cache_dir()
        if not d:
            return ""
        try:
            h = hashlib.sha1((url + "|" + (key_hex or "")).encode("utf-8")).hexdigest()
            return _os.path.join(d, "img_%s.bin" % h[:24])
        except Exception:
            return ""

    def _img_lock(self, ck):
        with self._lock:
            lk = self._img_locks.get(ck)
            if lk is None:
                lk = _threading.Lock()
                if len(self._img_locks) > 600:
                    self._img_locks.clear()
                self._img_locks[ck] = lk
            return lk

    def _img_fetch_decrypt(self, url, key_hex):
        """下载 + 解密 -> (bytes|None, ctype)。失败返回 (None, ctype)。"""
        raw = None
        try:
            raw = _http_get_full(url)
        except Exception:
            return None, "image/jpeg"
        if not raw:
            return None, "image/jpeg"
        if key_hex:
            try:
                raw = aes256_gcm_decrypt(raw, bytes.fromhex(key_hex))
            except Exception:
                return None, "image/jpeg"
        try:
            ctype = _img_mime(detect_image_format(raw, url))
        except Exception:
            ctype = "image/jpeg"
        return raw, ctype

    def _img_store(self, ck, data, ctype, disk_path=""):
        with self._lock:
            if len(self._imgs) >= _PROXY_IMG_MAX:
                self._imgs.clear()
            self._imgs[ck] = (data, ctype, _time.time())
        if disk_path:
            try:
                tmp = disk_path + ".%d.tmp" % _threading.get_ident()
                with open(tmp, "wb") as f:
                    f.write(data)
                _os.replace(tmp, disk_path)
            except Exception:
                pass

    def serve_image(self, handler, url, key_hex):
        if not url:
            handler._send(400, b"missing url", "text/plain")
            return
        key_hex = key_hex or ""
        ck = (url, key_hex)
        data, ctype = None, "image/jpeg"
        with self._lock:
            ent = self._imgs.get(ck)
            if ent and _time.time() - ent[2] < _PROXY_IMG_TTL:
                data, ctype = ent[0], ent[1]
        if data is not None:
            handler._send(200, data, ctype)
            return
        # 磁盘缓存
        disk_path = self._img_disk_path(url, key_hex)
        if disk_path:
            try:
                if _os.path.isfile(disk_path):
                    with open(disk_path, "rb") as f:
                        data = f.read()
                    try:
                        ctype = _img_mime(detect_image_format(data, url))
                    except Exception:
                        ctype = "image/jpeg"
                    self._img_store(ck, data, ctype)
                    handler._send(200, data, ctype)
                    return
            except Exception:
                data = None
        # 上游：加锁防同图并发重复下载解密
        lk = self._img_lock(ck)
        with lk:
            with self._lock:
                ent = self._imgs.get(ck)
                if ent and _time.time() - ent[2] < _PROXY_IMG_TTL:
                    data, ctype = ent[0], ent[1]
            if data is None:
                data, ctype = self._img_fetch_decrypt(url, key_hex)
                if data is None:
                    handler._send(502, b"upstream fetch failed", "text/plain")
                    return
                self._img_store(ck, data, ctype, disk_path)
        handler._send(200, data, ctype)

    def preload_images(self, pairs):
        """后台预加载漫画图片（pairs: [(url, key_hex)]）。守护线程 + 小并发池。"""
        if not pairs:
            return
        todo = []
        with self._lock:
            seen = self._preload_seen
            for u, k in pairs:
                if not u:
                    continue
                ck = (u, k or "")
                if ck in seen:
                    continue
                ent = self._imgs.get(ck)
                if ent and _time.time() - ent[2] < _PROXY_IMG_TTL:
                    seen.add(ck)
                    continue
                if self._img_disk_path(u, k or "") and _os.path.isfile(
                        self._img_disk_path(u, k or "")):
                    seen.add(ck)
                    continue
                seen.add(ck)
                todo.append(ck)
            if len(seen) > 4000:
                self._preload_seen = set(list(seen)[-2000:])
        if not todo:
            return
        todo = todo[:_PROXY_IMG_PRELOAD_MAX]

        def _work(ck):
            u, k = ck
            try:
                disk_path = self._img_disk_path(u, k)
                if disk_path and _os.path.isfile(disk_path):
                    return
                data, ctype = self._img_fetch_decrypt(u, k)
                if data:
                    self._img_store(ck, data, ctype, disk_path)
            except Exception:
                pass

        def _run():
            try:
                from concurrent.futures import ThreadPoolExecutor as _TPE
                with _TPE(max_workers=_PROXY_IMG_PRELOAD) as ex:
                    list(ex.map(_work, todo))
            except Exception:
                for ck in todo:
                    _work(ck)

        t = _threading.Thread(target=_run)
        t.daemon = True
        t.start()

    # ---------------- 缓存管理 ----------------
    def _cache_path(self, url):
        d = _proxy_cache_dir()
        if not d:
            return ""
        try:
            name = "v_%s.mp4" % hashlib.md5(url.encode("utf-8")).hexdigest()[:20]
            return _os.path.join(d, name)
        except Exception:
            return ""

    def _dl_lock(self, url):
        with self._lock:
            lk = self._dl_locks.get(url)
            if lk is None:
                lk = _threading.Lock()
                if len(self._dl_locks) > 200:
                    self._dl_locks.clear()
                self._dl_locks[url] = lk
            return lk

    def _cleanup_cache(self):
        d = _proxy_cache_dir()
        if not d:
            return
        try:
            now = _time.time()
            vids, imgs = [], []
            for name in _os.listdir(d):
                p = _os.path.join(d, name)
                try:
                    st = _os.stat(p)
                except Exception:
                    continue
                if name.startswith("img_") and name.endswith(".bin"):
                    if now - st.st_mtime > _PROXY_IMG_DISK_TTL:
                        try:
                            _os.remove(p)
                        except Exception:
                            pass
                        continue
                    imgs.append((st.st_mtime, p))
                elif name.startswith("v_") and name.endswith(".mp4"):
                    if now - st.st_mtime > _CACHE_TTL:
                        try:
                            _os.remove(p)
                        except Exception:
                            pass
                        continue
                    vids.append((st.st_mtime, p))
            for lst, cap in ((vids, _CACHE_MAX_FILES), (imgs, _CACHE_IMG_MAX_FILES)):
                lst.sort()
                while len(lst) > cap:
                    try:
                        _os.remove(lst.pop(0)[1])
                    except Exception:
                        lst.pop(0)
        except Exception:
            pass


# ===========================================================================
# Part 3 — TVBox Spider：五类内容路由
# ===========================================================================
try:
    from base.spider import Spider as _BaseSpider
except Exception:  # 脱离 TVBox 环境时提供最小桩，保证本文件可独立 import
    class _BaseSpider(object):
        def init(self, extend=""):
            pass

# 类型注册表：tab_type/bottom_tab_type 来自 bookmall；search_tab 来自搜索
_FQ_TYPES = {
    "novel": {"label": "小说", "tab": "25", "bottom": "1", "search": "3", "from": "番茄小说"},
    "short": {"label": "短剧", "tab": "8", "bottom": "7", "search": "11", "from": "番茄短剧"},
    "manga": {"label": "漫画", "tab": "9", "bottom": "1", "search": "8", "from": "番茄漫画"},
    "mdr": {"label": "漫剧", "tab": "24", "bottom": "7", "search": None, "from": "番茄漫剧"},
    "audio": {"label": "听书", "tab": "5", "bottom": "1", "search": "2", "from": "番茄听书"},
}

_FQ_HOME_ORDER = ["short", "novel", "manga", "mdr", "audio"]


def _fq_first_str(d, keys):
    for k in keys:
        v = d.get(k)
        if isinstance(v, str) and v.strip():
            return v.strip()
    return ""


def _fq_pic(d, keys):
    u = _fq_first_str(d, keys)
    if not u:
        return ""
    if u.startswith("http"):
        return u
    if u.startswith("//"):
        return "https:" + u
    return "https://p3-reading-sign.fqnovelpic.com/" + u.lstrip("/")


def _fq_walk_items(node, kind, out, depth=0):
    """递归收集书籍项（book_id+book_name）或视频项（vid+title）。"""
    if depth > 6:
        return
    if isinstance(node, dict):
        if kind == "book":
            bid = node.get("book_id")
            name = node.get("book_name") or node.get("title")
            if bid and name and isinstance(name, str):
                out.append(node)
                return
        else:
            vid = node.get("vid") or node.get("video_id")
            title = node.get("title")
            if vid and title and isinstance(title, str):
                out.append(node)
                return
        for k in ("book_data", "video_data", "cell_data", "data", "items"):
            v = node.get(k)
            if isinstance(v, list):
                for it in v:
                    _fq_walk_items(it, kind, out, depth + 1)
    elif isinstance(node, list):
        for it in node:
            _fq_walk_items(it, kind, out, depth + 1)


def _fq_vod_from_book(it, kind):
    bid = str(it.get("book_id") or "")
    name = str(it.get("book_name") or it.get("title") or "")
    return {
        "vod_id": "%s:%s" % (kind, bid),
        "vod_name": name,
        "vod_pic": _fq_pic(it, ("thumb_url", "cover", "detail_page_thumb_url",
                                "expand_thumb_url", "audio_thumb_url_hd")),
        "vod_remarks": str(it.get("author") or it.get("category") or ""),
        "vod_content": str(it.get("abstract") or it.get("book_abstract_v2") or "")[:200],
    }


def _fq_vod_from_video(it, kind):
    sid = str(it.get("series_id") or it.get("vid") or "")
    return {
        "vod_id": "%s:%s" % (kind, sid),
        "vod_name": str(it.get("title") or ""),
        "vod_pic": _fq_pic(it, ("cover", "horiz_cover", "episode_cover", "series_cover")),
        "vod_remarks": ("%s集" % it.get("episode_cnt")) if it.get("episode_cnt") else "",
        "vod_content": "",
    }


def _fq_vod_list(items, kind):
    out = []
    seen = set()
    for it in items:
        if kind in ("novel", "manga", "audio"):
            v = _fq_vod_from_book(it, kind)
        else:
            v = _fq_vod_from_video(it, kind)
        if not v["vod_id"] or v["vod_id"] in seen or not v["vod_name"]:
            continue
        seen.add(v["vod_id"])
        out.append(v)
    return out


def _fq_item_key(it, kind):
    """feed 项稳定 key（跨页去重用）。"""
    if kind in ("short", "mdr"):
        return "v:%s" % (it.get("series_id") or it.get("vid") or
                         it.get("video_id") or id(it))
    return "b:%s" % (it.get("book_id") or id(it))


class Spider(_BaseSpider):

    def __init__(self):
        self.box = None
        self.proxy = None
        self._tab_cells = {}   # kind -> (cell_id, ts)
        self._cell_lock = _threading.Lock()
        self._home_cache = None  # (list, ts)
        self._feed_cache = {}    # (kind, offset, sel) -> (items, has_more, next_offset, ts, ttl)
        self._feed_lock = _threading.Lock()
        self._cat_seen = {}      # kind -> set(已展示 vod_id)
        self._var_cache = {}     # sid -> (variants, ts)
        self._search_seen = {}   # (关键词, kind) -> set(已返回 vod_id)
        self._search_lock = _threading.Lock()
        # 视频类（short/mdr）crt=1 顺序 walk 缓冲：并发请求会互相踩服务端
        # 会话游标，必须串行；缓冲累积后对壳按 20 条/页切片，支持跳页。
        self._feed_buf = {}      # kind -> [item...]（顺序累积）
        self._feed_buf_ids = {}  # kind -> set(key) 已入缓冲
        self._feed_buf_off = {}  # kind -> 下一个要 walk 的 offset
        self._feed_buf_hm = {}   # kind -> has_more
        self._feed_buf_ts = {}   # kind -> 最近 walk 时间
        self._feed_buf_sel = {}  # kind -> 当前 selector_item_id
        self._feed_buf_sels = {} # kind -> [待切换 selector 队列]
        self._feed_buf_stale = {}  # kind -> 当前 selector 内连续零新增页数
        self._feed_buf_swcnt = {}  # kind -> 已切换 selector 次数
        self._feed_served = {}     # kind -> 已服务到的缓冲索引（短页接续用）
        self._walk_locks = {}    # kind -> Lock（保证同类串行）
        self._walk_started = set()  # 已启动后台 walker 的 kind
        self._walk_threads = {}  # kind -> Thread（存活判断用）

    # ---------------- 基础 ----------------
    def getName(self):
        return "番茄TV"

    def init(self, extend=""):
        try:
            super().init(extend)
        except Exception:
            pass
        try:
            if self.box is None:
                self.box = FqBox()
        except Exception:
            self.box = None
        if self.proxy is None:
            self.proxy = _FqProxy()
            self.proxy.box = self.box
            self.proxy.start()
        # 预热设备注册：壳清缓存后设备须重新注册（约 2~5s），这里后台先起步，
        # 让首屏并发请求与注册并行，避免每个请求各自排队等注册
        try:
            box = self.box
            if box is not None:
                def _warm():
                    try:
                        box.up.store.get()
                    except Exception:
                        pass
                t = _threading.Thread(target=_warm)
                t.daemon = True
                t.start()
        except Exception:
            pass

    def destroy(self):
        try:
            if self.proxy and self.proxy.server:
                self.proxy.server.shutdown()
        except Exception:
            pass

    def _box(self):
        if self.box is None:
            self.init()
        return self.box

    # ---------------- 首页 ----------------
    def homeContent(self, filter):
        classes = []
        for kind in _FQ_HOME_ORDER:
            classes.append({"type_id": kind, "type_name": _FQ_TYPES[kind]["label"]})
        lst = []
        try:
            lst = self._home_list()
        except Exception:
            lst = []
        return {"class": classes, "list": lst, "filters": {}}

    def _feed_raw(self, kind, offset="0", sel="", deadline=None):
        """feed 原始项（带 2 分钟缓存，首页与分类页共用）。
        -> (items, has_more, next_offset)；has_more=None 表示瞬时失败（未缓存）。
        sel 为 selector_item_id（短剧切换内容源用）。
        deadline：绝对时间戳；深翻页等有预算的场景按剩余时间动态压缩
        单次请求超时，避免 3×设备重试×15s 拖穿整个页等待预算。"""
        cfg = _FQ_TYPES.get(kind)
        if not cfg:
            return [], False, ""
        fcfg = _FQ_FEED.get(kind) or {"crt": "2", "step": 20}
        ck = (kind, str(offset), sel or "")
        with self._feed_lock:
            ent = self._feed_cache.get(ck)
            if ent and _time.time() - ent[3] < ent[4]:
                return ent[0], ent[1], ent[2]
        box = self._box()
        items, has_more, next_off = [], None, ""
        if box is not None:
            cid = self._tab_cell(kind)
            if cid:
                for attempt in range(3):
                    now = _time.time()
                    if deadline is not None and now > deadline:
                        break
                    # 有预算时单次请求超时随剩余预算收缩（下限 3s），
                    # 最坏页等待压在 budget+3s，而非 3 设备重试×15s
                    kw = {}
                    if deadline is not None:
                        kw["timeout"] = max(3.0, min(15.0, deadline - now))
                    try:
                        if sel:
                            r = box.series_feed(cid, tab_type=cfg["tab"],
                                                offset=str(offset),
                                                client_req_type=fcfg["crt"],
                                                selector_item_id=sel, **kw)
                        else:
                            r = box.series_feed(cid, tab_type=cfg["tab"],
                                                offset=str(offset),
                                                client_req_type=fcfg["crt"], **kw)
                        d = r.get("data") or {}
                        found = []
                        _fq_walk_items(d.get("cell_view"),
                                       "video" if kind in ("short", "mdr") else "book",
                                       found)
                        items = found
                        hm = d.get("has_more")
                        if isinstance(hm, bool):
                            has_more = hm
                        no = d.get("next_offset")
                        if isinstance(no, int):
                            next_off = str(no)
                        self._collect_selectors(kind, d)
                    except Exception:
                        items = []
                    if items:
                        break               # 成功
                    if attempt < 2:
                        if deadline is not None and _time.time() + 0.8 > deadline:
                            break
                        _time.sleep(0.8)    # 空结果（含服务端误报末尾）退避重试
                # 失败/空结果不写缓存（可能是上游限流），允许后续重试；
                # 仅「服务端明确告知没有更多」时才缓存空结果，且短 TTL 自愈
                # （上游偶发误报 has_more=False，30 秒后自动恢复）。
                if not items and has_more is not False:
                    return [], None, ""
        with self._feed_lock:
            if len(self._feed_cache) > 60:
                self._feed_cache.clear()
            ttl = _FEED_TTL if items else 30
            self._feed_cache[ck] = (items, has_more if has_more is not None else False,
                                    next_off, _time.time(), ttl)
        return items, (has_more if has_more is not None else False), next_off

    def _collect_selectors(self, kind, data):
        """从 feed 响应里收集 selector_item_id，并入该 kind 的待切换队列。"""
        with self._feed_lock:
            q = self._feed_buf_sels.get(kind)
            if q is not None and len(q) >= 24:
                return
        try:
            txt = _json.dumps(data)
        except Exception:
            return
        vals = _re.findall(r'"selector_item_id"\s*:\s*"([^"]+)"', txt)
        if not vals:
            return
        with self._feed_lock:
            q = self._feed_buf_sels.setdefault(kind, [])
            have = set(q) | {self._feed_buf_sel.get(kind) or ""}
            for v in vals:
                if v and v not in have and len(q) < 24:
                    q.append(v)
                    have.add(v)

    # ---------------- 视频类顺序 walk 缓冲 ----------------
    def _walk_lock(self, kind):
        with self._feed_lock:
            lk = self._walk_locks.get(kind)
            if lk is None:
                lk = _threading.Lock()
                self._walk_locks[kind] = lk
            return lk

    def _feed_walk_one(self, kind, deadline=None):
        """串行拉取下一个上游页并追加进缓冲（锁内完成，防并发互踩游标）。
        当前 selector 连续零新增时自动切换到下一个内容源（offset 归零重走）。
        deadline：有预算的同步补拉时传入，超预算即放弃本次（返回短页，
        由后台 walker 继续补足）。"""
        fcfg = _FQ_FEED.get(kind) or {"crt": "2", "step": 20}
        step = int(fcfg.get("step") or 20)
        with self._walk_lock(kind):
            with self._feed_lock:
                off = self._feed_buf_off.get(kind, 0)
                sel = self._feed_buf_sel.get(kind, "")
                stale = self._feed_buf_stale.get(kind, 0)
            items, has_more, _no = self._feed_raw(kind, str(off), sel,
                                                  deadline=deadline)
            added = 0
            with self._feed_lock:
                buf = self._feed_buf.setdefault(kind, [])
                seen = self._feed_buf_ids.setdefault(kind, set())
                for it in items:
                    k = _fq_item_key(it, kind)
                    if k in seen:
                        continue
                    seen.add(k)
                    buf.append(it)
                    added += 1
                self._feed_buf_ts[kind] = _time.time()
                # 枯竭判定：同一 selector 探够深度且连续零新增、服务端仍称
                # 有更多 -> 换下一个内容源（off 归零重走）
                stale = 0 if added else stale + 1
                switched = False
                if (stale >= _FEED_STALE_MAX and has_more is not False
                        and off >= _FEED_SEL_MIN_OFF
                        and self._feed_buf_swcnt.get(kind, 0) < _FEED_SEL_MAX_SWITCH):
                    q = self._feed_buf_sels.get(kind) or []
                    while q:
                        nxt = q.pop(0)
                        # 跳过等价于当前默认源的项（初始 sel="" 即 hot 源）
                        if not nxt or nxt == sel:
                            continue
                        if not sel and nxt == "videoseries_hot_v2":
                            continue
                        self._feed_buf_sel[kind] = nxt
                        self._feed_buf_swcnt[kind] = \
                            self._feed_buf_swcnt.get(kind, 0) + 1
                        off = 0
                        switched = True
                        break
                    if switched:
                        stale = 0
                if not switched:
                    # 连续零新增时加速跨过重复区（服务端补批有固定 offset 边界）
                    off = off + (step * 3 if stale >= _FEED_STALE_MAX else step)
                self._feed_buf_off[kind] = off
                self._feed_buf_stale[kind] = stale
                self._feed_buf_hm[kind] = has_more
        return added, has_more

    def _feed_walk_ensure(self, kind, need, budget=_FEED_ENSURE_BUDGET):
        """确保缓冲至少 need 条。
        walker 存活时只等待让权（单管道全速，避免两方抢锁互相稀释）；
        walker 未运行/已退出时当前线程自己串行补拉（deadline 下沉到
        _feed_raw，单次请求超时随剩余预算收缩，最坏等待≈budget+3s）。
        has_more=None（瞬时失败/限流）退避重试；超预算返回短页，
        由 walker 后台补足（壳回翻该页即完整）。"""
        deadline = _time.time() + budget
        while True:
            with self._feed_lock:
                have = len(self._feed_buf.get(kind) or [])
                hm = self._feed_buf_hm.get(kind)
                off = self._feed_buf_off.get(kind, 0)
                wt = self._walk_threads.get(kind)
                walker_alive = bool(wt is not None and wt.is_alive())
            if have >= need or hm is False or off > 6000:
                return
            if _time.time() > deadline:
                return
            if walker_alive:
                _time.sleep(0.15)
                continue
            added, hm2 = self._feed_walk_one(kind, deadline=deadline)
            if hm2 is None and not added:
                if _time.time() > deadline:
                    return
                _time.sleep(1.0)   # 限流退避后由外层循环重试
                continue

    def _feed_walk_start(self, kind):
        """启动后台 walk 守护线程（一次性；填满 _FEED_BUF_MAX 或 has_more=False）。"""
        with self._feed_lock:
            if kind in self._walk_started:
                return
            self._walk_started.add(kind)
            # 短剧有 selector 内容源；枯竭切换用。兜底列表置顶，响应里
            # 收集到的值去重后追加（收集值可能含无效源，故排在兜底之后）。
            if kind == "short":
                q = self._feed_buf_sels.setdefault(kind, [])
                for v in reversed(_FQ_SELECTORS):
                    if v not in q:
                        q.insert(0, v)

        def _run():
            fails = 0
            try:
                while True:
                    with self._feed_lock:
                        have = len(self._feed_buf.get(kind) or [])
                        hm = self._feed_buf_hm.get(kind)
                        off = self._feed_buf_off.get(kind, 0)
                    if have >= _FEED_BUF_MAX or hm is False or off > 6000:
                        return
                    added, hm2 = self._feed_walk_one(kind)
                    if hm2 is None and not added:
                        fails += 1
                        if fails >= 10:
                            return
                        _time.sleep(1.0)   # 限流退避
                        continue
                    fails = 0
                    _time.sleep(0.15)   # 温和限速：别把上游配额全吃光
            except Exception:
                pass

        t = _threading.Thread(target=_run)
        t.daemon = True
        with self._feed_lock:
            self._walk_threads[kind] = t
        t.start()

    def _feed_page(self, kind, pg, need=None, start_walker=True, fast_first=True):
        """壳页 -> (vod_list, has_more)。
        视频类（crt=1）走顺序 walk 缓冲切 _FEED_PAGE 条；书籍类（crt=2）offset 页直取。
        need 可覆盖所需条数（首页只取少量，避免无谓串行等待）。
        start_walker=False 时只同步补拉不起后台线程（首页用：避免首页
        返回后 walker 持续吃上游配额，把用户随后的分类页请求挤到短页）。
        fast_first：分类首屏保底出货（不憋满 20 条），首页传 False 按 need 取满。"""
        fcfg = _FQ_FEED.get(kind) or {"crt": "2", "step": 20}
        step = int(fcfg.get("step") or 20)
        pg = pg if pg and pg > 0 else 1
        if fcfg.get("crt") != "1":
            items, has_more, _no = self._feed_raw(kind, str((pg - 1) * step))
            return _fq_vod_list(items, kind), (True if has_more is None else has_more)
        if need is None:
            need = pg * _FEED_PAGE
        if pg == 1 and fast_first:
            # 首屏：同样凑满 20 条，但等待上限 8s（旧 15s），超时按实际出货
            self._feed_walk_ensure(kind, need, budget=_FEED_ENSURE_FIRST_BUDGET)
        else:
            self._feed_walk_ensure(kind, need)
        if start_walker:
            self._feed_walk_start(kind)
        with self._feed_lock:
            buf = list(self._feed_buf.get(kind) or [])
            hm = self._feed_buf_hm.get(kind, True)
            served = self._feed_served.get(kind, 0)
        # 前进时若前几页是短页（walker 未补够），从已服务索引接续，
        # 避免短页边界把缓冲中间的条目永久跳过；回翻则按 pg 对齐。
        start = (pg - 1) * _FEED_PAGE
        if start > served:
            start = max(start, served)
        chunk = buf[start:start + _FEED_PAGE]
        if chunk:
            with self._feed_lock:
                self._feed_served[kind] = start + len(chunk)
        return _fq_vod_list(chunk, kind), hm

    def _home_list(self):
        if self._home_cache and _time.time() - self._home_cache[1] < _HOME_TTL:
            return self._home_cache[0]
        box = self._box()
        if box is None:
            return []
        plans = [("short", 12), ("novel", 10), ("manga", 10),
                 ("mdr", 8), ("audio", 8)]
        out = []

        def _fetch(plan):
            kind, n = plan
            try:
                lst, _hm = self._feed_page(kind, 1, need=n, start_walker=False,
                                           fast_first=False)
                return lst[:n]
            except Exception:
                return []

        try:
            from concurrent.futures import ThreadPoolExecutor as _TPE
            with _TPE(max_workers=len(plans)) as ex:
                results = list(ex.map(_fetch, plans))
        except Exception:
            results = [_fetch(p) for p in plans]
        for r in results:
            out.extend(r)
        self._home_cache = (out, _time.time())
        return out

    def homeVodContent(self, filter):
        try:
            return {"list": self._home_list(), "page": 1, "pagecount": 1,
                    "limit": 30, "total": 30}
        except Exception:
            return {"list": []}

    def _tab_cell(self, kind):
        """取该类型的首个 cell_id（内存 10 分钟 + 磁盘 6 小时缓存）。
        失败绝不写缓存：冷启动瞬措/限流时若把空 cid 缓存起来，分类会
        连续空 10 分钟（旧 bug：用户“第一次没内容、清后台重进几次才有”
        正是空 cid 被缓存，重进=新进程=缓存清空后才好）。"""
        cfg = _FQ_TYPES.get(kind)
        if not cfg:
            return ""
        with self._cell_lock:
            ent = self._tab_cells.get(kind)
            if ent and _time.time() - ent[1] < 600:
                return ent[0]
        now = _time.time()
        # 磁盘缓存（与设备缓存同目录）：清后台重进不再重拉 tab，
        # 首页/分类冷启动省去每类 1~2s 的 tab 请求
        cid = ""
        try:
            with open(_tabcell_cache_path(), "r", encoding="utf-8") as f:
                disk = _json.load(f)
            ent = disk.get(kind) if isinstance(disk, dict) else None
            if (isinstance(ent, list) and len(ent) == 2 and ent[0]
                    and now - float(ent[1]) < _TABCELL_TTL):
                cid = str(ent[0])
        except Exception:
            pass
        if cid:
            with self._cell_lock:
                self._tab_cells[kind] = (cid, now)
            return cid
        try:
            box = self._box()
            if box is not None:
                r = box.bookmall_tab(tab_type=cfg["tab"], bottom_tab_type=cfg["bottom"],
                                     client_req_type="3")
                for it in ((r.get("data") or {}).get("tab_item") or []):
                    if str(it.get("tab_type")) == cfg["tab"]:
                        cd = it.get("cell_data")
                        if isinstance(cd, list) and cd and isinstance(cd[0], dict):
                            v = cd[0].get("cell_id")
                            if v:
                                cid = str(v)
                        break
        except Exception:
            cid = ""
        if cid:                       # 仅成功才写缓存（内存+磁盘）
            with self._cell_lock:
                self._tab_cells[kind] = (cid, _time.time())
            _tabcell_save(kind, cid)
        return cid

    # ---------------- 分类 ----------------
    def categoryContent(self, tid, pg, filter, extend):
        try:
            pgn = int(pg) if pg else 1
        except Exception:
            pgn = 1
        if pgn < 1:
            pgn = 1
        kind = str(tid or "")
        if kind not in _FQ_TYPES:
            kind = "short"
        lst, has_more = [], True
        try:
            lst, has_more = self._feed_page(kind, pgn)
        except Exception:
            lst = []
        pagecount = 999 if has_more is not False else pgn
        return {"list": lst, "page": pgn, "pagecount": pagecount,
                "limit": _FEED_PAGE, "total": 9999 if has_more is not False else (pgn - 1) * _FEED_PAGE + len(lst)}

    # ---------------- 详情 ----------------
    def detailContent(self, ids):
        try:
            return self._detail(ids)
        except Exception as e:
            vid = str(ids[0]) if isinstance(ids, list) and ids else str(ids or "")
            return {"list": [{
                "vod_id": vid, "vod_name": "【解析异常】", "vod_pic": "",
                "vod_content": ("%s" % e)[:300],
                "vod_play_from": "番茄TV", "vod_play_url": "异常",
            }]}

    def _detail(self, ids):
        if isinstance(ids, list):
            ids = ids[0] if ids else ""
        raw = str(ids or "")
        if ":" in raw:
            kind, bid = raw.split(":", 1)
        else:
            kind, bid = "short", raw
        kind = kind if kind in _FQ_TYPES else "short"
        bid = (bid or "").strip()
        if not bid:
            return {"list": [{
                "vod_id": raw, "vod_name": "【参数错误】", "vod_pic": "",
                "vod_content": "id 不能为空", "vod_play_from": "番茄TV",
                "vod_play_url": "无",
            }]}
        box = self._box()
        if box is None:
            return {"list": []}
        cfg = _FQ_TYPES[kind]

        if kind in ("short", "mdr"):
            return self._detail_video(box, bid, kind, cfg)
        return self._detail_book(box, bid, kind, cfg)

    def _detail_book(self, box, bid, kind, cfg):
        info = {}
        try:
            d = box.book_detail_legacy(bid)
            info = (d.get("data") or {}) if isinstance(d, dict) else {}
        except Exception:
            info = {}
        name = str(info.get("book_name") or "")
        if not name:
            name = bid
        cover = _fq_pic(info, ("thumb_url", "cover", "detail_page_thumb_url"))
        abstract = str(info.get("abstract") or "")
        author = str(info.get("author") or "")
        category = str(info.get("category") or info.get("tags") or "")
        remarks = str(info.get("score") or "")
        status = str(info.get("creation_status") or "")
        if status == "0":
            remarks = (remarks + " 连载中").strip()
        elif status == "1":
            remarks = (remarks + " 已完结").strip()

        # 章节目录
        chapters = []
        try:
            d = box.directory_reading(bid)
            data = (d.get("data") or {}) if isinstance(d, dict) else {}
            for key in ("item_data_list", "item_list"):
                v = data.get(key)
                if isinstance(v, list) and v:
                    chapters = v
                    break
        except Exception:
            chapters = []

        urls = []
        for ch in chapters:
            if not isinstance(ch, dict):
                continue
            item_id = ch.get("item_id")
            if not item_id:
                continue
            title = str(ch.get("title") or "")
            if kind == "novel":
                pid = "novel:%s@@%s@@%s" % (bid, item_id, title)
            elif kind == "manga":
                pid = "manga:%s@@full" % item_id
            else:
                pid = "audio:%s@@%s" % (bid, item_id)
            urls.append("%s$%s" % (title or "章节", pid))

        if not urls:
            return {"list": [{
                "vod_id": "%s:%s" % (kind, bid), "vod_name": name,
                "vod_pic": cover, "vod_content": abstract[:300],
                "vod_play_from": cfg["from"], "vod_play_url": "暂无章节",
            }]}

        return {"list": [{
            "vod_id": "%s:%s" % (kind, bid),
            "vod_name": name,
            "vod_pic": cover,
            "type_name": cfg["label"],
            "vod_year": "",
            "vod_area": "",
            "vod_remarks": remarks,
            "vod_actor": author,
            "vod_director": author,
            "vod_content": abstract[:500],
            "vod_play_from": cfg["from"],
            "vod_play_url": "#".join(urls),
        }]}

    def _video_variants(self, vid):
        """首集清晰度列表（5 分钟缓存）-> [{"name","width","height","url","key_hex"}] 画质降序。"""
        if not vid:
            return []
        with self._feed_lock:
            ent = self._var_cache.get(vid)
            if ent and _time.time() - ent[1] < _VAR_TTL:
                return ent[0]
        box = self._box()
        variants = []
        if box is not None:
            try:
                _u, _k, variants = box.resolve_video(vid, stream=True)
            except Exception:
                variants = []
        variants = [v for v in (variants or [])
                    if isinstance(v, dict) and v.get("url") and v.get("name")]
        with self._feed_lock:
            if len(self._var_cache) > 60:
                self._var_cache.clear()
            self._var_cache[vid] = (variants, _time.time())
        return variants

    def _detail_video(self, box, sid, kind, cfg):
        info = {}
        episodes = []
        try:
            d = box.video_detail(sid)
            vd = ((d.get("data") or {}).get("video_data")) or {}
            info = vd if isinstance(vd, dict) else {}
            vl = info.get("video_list")
            if isinstance(vl, list):
                episodes = vl
            elif isinstance(vl, dict):
                episodes = [v for v in vl.values() if isinstance(v, dict)]
        except Exception:
            episodes = []
        name = str(info.get("series_title") or info.get("title") or sid)
        cover = _fq_pic(info, ("series_cover", "cover"))
        abstract = str(info.get("abstract") or "")
        cnt = info.get("episode_cnt") or len(episodes)
        remarks = ("%s集" % cnt) if cnt else ""

        vids = []
        for ep in episodes:
            if not isinstance(ep, dict):
                continue
            vid = ep.get("vid") or ep.get("video_id")
            if not vid:
                continue
            idx = ep.get("vid_index")
            try:
                idx = int(idx)
            except Exception:
                idx = len(vids) + 1
            vids.append((idx, str(vid)))
        if not vids:
            return {"list": [{
                "vod_id": "%s:%s" % (kind, sid), "vod_name": name,
                "vod_pic": cover, "vod_content": abstract[:300],
                "vod_play_from": cfg["from"], "vod_play_url": "暂无剧集",
            }]}

        # 清晰度多线路（红果模式）：用首集 variants 建 $$$ 线路，集 id 带 |清晰度名
        variants = []
        try:
            variants = self._video_variants(vids[0][1])
        except Exception:
            variants = []
        sources = []
        if variants:
            for v in variants:
                qname = v.get("name") or ""
                eps = ["第%s集$video:%s|%s" % (idx, vid, qname)
                       for idx, vid in vids]
                sources.append({"name": qname, "episodes": "#".join(eps)})
        if not sources:
            eps = ["第%s集$video:%s" % (idx, vid) for idx, vid in vids]
            sources = [{"name": cfg["from"], "episodes": "#".join(eps)}]
        return {"list": [{
            "vod_id": "%s:%s" % (kind, sid),
            "vod_name": name,
            "vod_pic": cover,
            "type_name": cfg["label"],
            "vod_year": "",
            "vod_area": "",
            "vod_remarks": remarks,
            "vod_actor": "",
            "vod_director": "",
            "vod_content": abstract[:500],
            "vod_play_from": "$$$".join(s["name"] for s in sources),
            "vod_play_url": "$$$".join(s["episodes"] for s in sources),
        }]}

    # ---------------- 搜索 ----------------
    def _search_seen_set(self, ck):
        with self._search_lock:
            s = self._search_seen.get(ck)
            if s is None:
                if len(self._search_seen) > 24:
                    self._search_seen.clear()
                s = set()
                self._search_seen[ck] = s
            return s

    def searchContent(self, key, quick, pg="1"):
        try:
            pgn = int(pg) if pg else 1
        except Exception:
            pgn = 1
        wd = str(key or "").strip()
        if not wd:
            return {"list": [], "page": pgn, "pagecount": 0, "limit": 20, "total": 0}
        box = self._box()
        out = []
        if box is not None:
            # 漫剧无独立搜索 tab（上游 9 个 tab 里没有 24），但 tab=11 的视频搜索
            # 能搜到漫剧，且与短剧共用详情/播放链路，故统一按 short 处理。
            plans = [("3", "novel"), ("11", "short"), ("8", "manga"), ("2", "audio")]
            for tab, kind in plans:
                try:
                    r = box.search_reading(wd, offset=str((pgn - 1) * 10),
                                           tab_type=tab)
                    items = []
                    for t in (r.get("search_tabs") or []):
                        data = t.get("data")
                        if not isinstance(data, list):
                            continue
                        for cell in data:
                            found = []
                            _fq_walk_items(cell, "book" if kind != "short" else "video",
                                           found, 0)
                            if found:
                                items.append(found[0])
                    # 页间去重（服务端游标跨页偶发 1 条重复）+ 每类配额
                    seen = self._search_seen_set((wd, kind))
                    if pgn <= 1:
                        seen.clear()
                    kept = []
                    for v in _fq_vod_list(items, kind):
                        if v["vod_id"] in seen:
                            continue
                        seen.add(v["vod_id"])
                        kept.append(v)
                        if len(kept) >= _SEARCH_PER_KIND:
                            break
                    out.extend(kept)
                except Exception:
                    continue
        return {"list": out[:60], "page": pgn,
                "pagecount": 999 if out else 0, "limit": 20,
                "total": 9999 if out else 0}

    def searchContentPage(self, key, quick, pg="1"):
        return self.searchContent(key, quick, pg)

    # ---------------- 播放 ----------------
    def playerContent(self, flag, id, vipFlags):
        try:
            return self._player(flag, id, vipFlags)
        except Exception as e:
            import traceback
            tb = traceback.format_exc().strip().split("\n")
            msg = "【异常】%s: %s\n%s" % (type(e).__name__, str(e)[:100],
                                         "\n".join(tb[-3:]))
            payload = _json.dumps({"title": "错误", "content": msg}, ensure_ascii=False)
            return {"parse": 0, "url": "novel://" + payload, "header": "", "jx": 0}

    def _proxy(self):
        if self.proxy is None or not self.proxy._started:
            self.init()
        return self.proxy

    def _player(self, flag, id, vipFlags):
        raw = str(id or "")
        # 兼容两种调用：TVBox 传 "video:xxx|q"，部分壳传整条 "第1集$video:xxx|q"
        if "$" in raw:
            _head, tail = raw.rsplit("$", 1)
            if tail.startswith(("video:", "novel:", "manga:", "audio:")):
                raw = tail
        if raw.startswith("novel:"):
            return self._play_novel(raw[6:])
        if raw.startswith("manga:"):
            return self._play_manga(raw[6:])
        if raw.startswith("audio:"):
            return self._play_audio(raw[6:])
        if raw.startswith("video:"):
            return self._play_video(raw[6:])
        # 兜底：按 flag 猜
        f = str(flag or "")
        if "小说" in f:
            return self._play_novel(raw)
        if "漫画" in f or "漫剧" in f:
            return self._play_manga(raw)
        if "听书" in f:
            return self._play_audio(raw)
        return self._play_video(raw)

    def _play_novel(self, payload):
        parts = payload.split("@@")
        book_id = parts[0] if parts else ""
        item_id = parts[1] if len(parts) > 1 else ""
        title = parts[2] if len(parts) > 2 else ""
        if not book_id or not item_id:
            return {"parse": 0, "url": "novel://" + _json.dumps(
                {"title": "错误", "content": "参数不完整"}, ensure_ascii=False)}
        box = self._box()
        text = ""
        if box is not None:
            try:
                text = box.novel_chapter(book_id, item_id)
            except Exception:
                text = ""
        if not text:
            text = "正文获取失败，请重试。"
        body = _json.dumps({"title": title or "章节", "content": text}, ensure_ascii=False)
        return {"parse": 0, "url": "novel://" + body, "header": "", "jx": 0}

    def _play_manga(self, payload):
        parts = payload.split("@@")
        item_id = parts[0] if parts else ""
        api_type = parts[1] if len(parts) > 1 and parts[1] else "full"
        box = self._box()
        proxy = self._proxy()
        if not box or not item_id:
            return self._play_empty()
        try:
            ch = box.manga_chapter(item_id, api_type)
        except Exception:
            return self._play_empty()
        pic_urls = ch.get("pic_urls") or []
        key_hex = ch.get("encrypt_key") or ""
        if not pic_urls:
            return self._play_empty()
        if proxy and proxy._started and key_hex:
            imgs = [proxy.img_url(u, key_hex) for u in pic_urls]
            try:
                proxy.preload_images([(u, key_hex) for u in pic_urls])
            except Exception:
                pass
        else:
            imgs = pic_urls
        return {
            "parse": 0, "playUrl": "", "url": "pics://" + "&&".join(imgs),
            "header": _json.dumps({"User-Agent": UA_WINDOWS_BROWSER}), "jx": 0,
        }

    def _play_audio(self, payload):
        parts = payload.split("@@")
        book_id = parts[0] if parts else ""
        item_id = parts[1] if len(parts) > 1 else ""
        box = self._box()
        proxy = self._proxy()
        if not box or not book_id or not item_id or not proxy or not proxy._started:
            return self._play_empty()
        try:
            url, key_hex = box.audio_chapter_stream(book_id, item_id)
        except Exception:
            return self._play_empty()
        if not url:
            return self._play_empty()
        return {"parse": 0, "playUrl": "", "url": proxy.stream_url(url, key_hex or ""),
                "header": _json.dumps({"User-Agent": UA_WINDOWS_BROWSER}), "jx": 0}

    def _play_video(self, vid):
        proxy = self._proxy()
        if not proxy or not proxy._started or not vid:
            return self._play_empty()
        q = ""
        if "|" in vid:
            vid, q = vid.split("|", 1)
            vid = vid.strip()
            q = q.strip()
        return {"parse": 0, "playUrl": "", "url": proxy.play_url(vid, q),
                "header": _json.dumps({"User-Agent": UA_WINDOWS_BROWSER}), "jx": 0}

    @staticmethod
    def _play_empty():
        return {"parse": 1, "playUrl": "", "url": "", "header": "", "jx": 0}

    def localProxy(self, params):
        return {"url": ""}
