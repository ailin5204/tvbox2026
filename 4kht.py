# -*- coding: utf-8 -*-
import sys
import ssl

# 1. 强制 UTF-8 编码，防中文报错
if sys.version_info[0] >= 3:
    try:
        sys.stdout.reconfigure(encoding='utf-8')
        sys.stderr.reconfigure(encoding='utf-8')
    except Exception:
        pass

# 2. 忽略 SSL 证书校验，防电视系统证书过期导致网络请求失败
try:
    ssl._create_default_https_context = ssl._create_unverified_context
except Exception:
    pass

# ----------------- 兼容补丁结束 -----------------
import base64
import json
import random
import re
import struct
import time
import uuid

try:
    import requests
except Exception:
    requests = None

try:
    from Crypto.Cipher import AES, PKCS1_v1_5
    from Crypto.PublicKey import RSA
    from Crypto.Util.Padding import pad, unpad
except Exception:
            # ===== 纯 Python 加密回退（缺 pycryptodome 时启用）=====
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
        0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16,
    ]
    _INV = [0] * 256
    for _i, _v in enumerate(_SBOX):
        _INV[_v] = _i
    _RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36]


    def _xt(a):
        return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff


    def _gm(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a = _xt(a)
            b >>= 1
        return r & 0xff


    def _expand(key):
        nk = len(key) // 4
        nr = nk + 6
        w = [list(key[i * 4:i * 4 + 4]) for i in range(nk)]
        for i in range(nk, 4 * (nr + 1)):
            t = list(w[i - 1])
            if i % nk == 0:
                t = t[1:] + t[:1]
                t = [_SBOX[x] for x in t]
                t[0] ^= _RCON[i // nk - 1]
            elif nk > 6 and i % nk == 4:
                t = [_SBOX[x] for x in t]
            w.append([w[i - nk][j] ^ t[j] for j in range(4)])
        return w, nr


    def _enc_block(block, w, nr):
        s = [[block[c * 4 + r] for r in range(4)] for c in range(4)]
        for c in range(4):
            for r in range(4):
                s[c][r] ^= w[c][r]
        for rnd in range(1, nr + 1):
            for c in range(4):
                for r in range(4):
                    s[c][r] = _SBOX[s[c][r]]
            for r in range(1, 4):
                row = [s[c][r] for c in range(4)]
                for c in range(4):
                    s[c][r] = row[(c + r) % 4]
            if rnd != nr:
                for c in range(4):
                    a = [s[c][r] for r in range(4)]
                    s[c][0] = _gm(a[0], 2) ^ _gm(a[1], 3) ^ a[2] ^ a[3]
                    s[c][1] = a[0] ^ _gm(a[1], 2) ^ _gm(a[2], 3) ^ a[3]
                    s[c][2] = a[0] ^ a[1] ^ _gm(a[2], 2) ^ _gm(a[3], 3)
                    s[c][3] = _gm(a[0], 3) ^ a[1] ^ a[2] ^ _gm(a[3], 2)
            for c in range(4):
                for r in range(4):
                    s[c][r] ^= w[rnd * 4 + c][r]
        return bytes(s[c][r] for c in range(4) for r in range(4))


    def _dec_block(block, w, nr):
        s = [[block[c * 4 + r] for r in range(4)] for c in range(4)]
        for c in range(4):
            for r in range(4):
                s[c][r] ^= w[nr * 4 + c][r]
        for rnd in range(nr - 1, 0, -1):
            for r in range(1, 4):
                row = [s[c][r] for c in range(4)]
                for c in range(4):
                    s[c][r] = row[(c - r) % 4]
            for c in range(4):
                for r in range(4):
                    s[c][r] = _INV[s[c][r]]
            for c in range(4):
                for r in range(4):
                    s[c][r] ^= w[rnd * 4 + c][r]
            for c in range(4):
                a = [s[c][r] for r in range(4)]
                s[c][0] = _gm(a[0],14) ^ _gm(a[1],11) ^ _gm(a[2],13) ^ _gm(a[3],9)
                s[c][1] = _gm(a[0],9) ^ _gm(a[1],14) ^ _gm(a[2],11) ^ _gm(a[3],13)
                s[c][2] = _gm(a[0],13) ^ _gm(a[1],9) ^ _gm(a[2],14) ^ _gm(a[3],11)
                s[c][3] = _gm(a[0],11) ^ _gm(a[1],13) ^ _gm(a[2],9) ^ _gm(a[3],14)
        for r in range(1, 4):
            row = [s[c][r] for c in range(4)]
            for c in range(4):
                s[c][r] = row[(c - r) % 4]
        for c in range(4):
            for r in range(4):
                s[c][r] = _INV[s[c][r]]
        for c in range(4):
            for r in range(4):
                s[c][r] ^= w[c][r]
        return bytes(s[c][r] for c in range(4) for r in range(4))


    class _AES(object):
        block_size = 16
        MODE_ECB = 1
        MODE_CBC = 2

        def __init__(self, key, mode, iv=None):
            key = bytes(key)
            if len(key) not in (16, 24, 32):
                raise ValueError('AES key must be 16/24/32 bytes, got %d' % len(key))
            self._w, self._nr = _expand(key)
            self._mode = mode
            self._iv = bytes(iv)[:16] if iv is not None else bytes(16)

        def encrypt(self, data):
            data = bytes(data)
            if len(data) % 16:
                raise ValueError('data not padded')
            out = b''
            prev = self._iv
            for i in range(0, len(data), 16):
                blk = data[i:i + 16]
                if self._mode == 2:
                    blk = bytes(a ^ b for a, b in zip(blk, prev))
                enc = _enc_block(blk, self._w, self._nr)
                out += enc
                prev = enc
            return out

        def decrypt(self, data):
            data = bytes(data)
            out = b''
            prev = self._iv
            for i in range(0, len(data), 16):
                blk = bytes(data[i:i + 16])
                dec = _dec_block(blk, self._w, self._nr)
                if self._mode == 2:
                    dec = bytes(a ^ b for a, b in zip(dec, prev))
                out += dec
                prev = blk
            return out

        @staticmethod
        def new(key, mode, iv=None):
            return _AES(key, mode, iv)


    AES = _AES


    def pad(data, block_size=16):
        data = bytes(data)
        n = block_size - (len(data) % block_size)
        return data + bytes([n]) * n


    def unpad(data, block_size=16):
        data = bytes(data)
        if not data:
            return data
        n = data[-1]
        if 0 < n <= block_size:
            return data[:-n]
        return data


    def _der(buf, pos=0):
        tag = buf[pos]
        pos += 1
        ln = buf[pos]
        pos += 1
        if ln & 0x80:
            k = ln & 0x7f
            ln = int.from_bytes(buf[pos:pos + k], 'big')
            pos += k
        return tag, buf[pos:pos + ln], pos + ln


    class _RSAKey(object):
        def __init__(self, n, e):
            self.n = n
            self.e = e
            self.size_in_bits = n.bit_length()

        def size_in_bytes(self):
            return (self.size_in_bits + 7) // 8


    class RSA(object):
        @staticmethod
        def import_key(extern_key):
            raw = extern_key
            if isinstance(raw, str):
                raw = base64.b64decode(raw)
            _t, body_, _e = _der(raw)
            _t1, _b1, p = _der(body_, 0)
            _t2, b2, p = _der(body_, p)
            _t3, b3, _e2 = _der(b2[1:])
            _tn, bn, q = _der(b3, 0)
            _te, be, q = _der(b3, q)
            return _RSAKey(int.from_bytes(bn, 'big'), int.from_bytes(be, 'big'))


    class _PKCS1Cipher(object):
        def __init__(self, key):
            self._key = key

        def encrypt(self, message):
            import os
            k = self._key.size_in_bytes()
            m = bytes(message)
            if len(m) > k - 11:
                raise ValueError('message too long')
            ps = bytearray()
            need = k - len(m) - 3
            while len(ps) < need:
                b = os.urandom(1)[0]
                if b:
                    ps.append(b)
            em = b'\x00\x02' + bytes(ps) + b'\x00' + m
            c = pow(int.from_bytes(em, 'big'), self._key.e, self._key.n)
            return c.to_bytes(k, 'big')


    class PKCS1_v1_5(object):
        @staticmethod
        def new(key):
            return _PKCS1Cipher(key)
try:
    from base.spider import Spider as BaseSpider
except Exception:
    class BaseSpider(object):
        pass

class Spider(BaseSpider):
    CONFIG = {
        "appName": "河豚",
        "publicKey": "MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQCr8SzZhjYy+rsya1K09t8d2K50pWFoBkgUqMpKOiW+3IEVKd4eTdvg9RSOjQ82kypL6R9BnsmrS1V8s4PVDwjQbUtYhTPPC9Hz16qY7rpD6m0d2vr09/UpWQ5uOy9PR0QTrsioveZ+DIe9jc3C+zBCu/kZSY/R8stwJoiitki3gwIDAQAB",
        "mSafeCode": "V04XQZNYRWN6T0JODZFIAG5CTZB3PT0=",
        "dataIv": "OC1A06E197EF10CF3F6058CA7A803B5E",
        "pkg": "com.djlxxl.xcydzkj",
        "host": "https://az1-1456692500.cos.ap-guangzhou.myqcloud.com/az1.txt",
        "vName": "7.0.0.2",
        "from": "蓝光4k,蓝光"
    }

    def getName(self):
        return self.cfg.get("appName", "河豚")

    def init(self, extend=""):
        self.cfg = dict(self.CONFIG)
        if isinstance(extend, str) and '$' in extend:
            path, key = extend.split('$', 1)
            ext = self._load_config(path.strip(), key.strip())
            if isinstance(ext, dict):
                self.cfg.update(ext)
            elif ext:
                self.cfg['host'] = str(ext).strip()
        elif isinstance(extend, dict):
            self.cfg.update(extend)
        elif isinstance(extend, str) and extend.strip():
            try:
                self.cfg.update(json.loads(extend)) if extend.startswith('{') else setattr(self, 'host', extend.strip())
            except:
                self.cfg['host'] = extend.strip()

        self.host = str(self.cfg.get("host", "")).rstrip("/")
        self.public_key = str(self.cfg.get("publicKey", ""))
        self.data_key = str(self.cfg.get("mSafeCode", ""))
        self.data_iv = str(self.cfg.get("dataIv", ""))
        self.common_key = "ed5fdsgucxumegqa"
        self.version = str(self.cfg.get("vName", "3.0.2.1"))
        self.session = requests.Session() if requests else None
        self.dynamic_key = ""

        from_config = self.cfg.get("from", "")
        self.line_order, self.line_block = [], []
        if from_config and '@' in from_config:
            parts = from_config.split('@')
            if parts[0].strip():
                self.line_order = [k.strip() for k in re.split(r',|@@', parts[0]) if k.strip()]
            if len(parts) > 1 and parts[1].strip():
                self.line_block = [k.strip() for k in re.split(r',|@@', parts[1]) if k.strip()]
        elif from_config:
            self.line_order = [k.strip() for k in re.split(r',|@@', from_config) if k.strip()]

        if self.host and self.session and self.host.endswith(('.txt', '.json')):
            try:
                domain = self.session.get(self.host, timeout=12).json().get("domain", "").strip().rstrip("/")
                if domain:
                    self.host = domain
            except:
                pass

        if self.host:
            try:
                self._load_dynamic_key()
            except:
                pass

    def _load_config(self, config_path, config_key=None):
        try:
            fetcher = self.fetch if hasattr(self, 'fetch') else lambda url, **kw: requests.get(url, timeout=12)
            content = fetcher(config_path, headers={}).text
            try:
                config = json.loads(content)
            except:
                content = re.sub(r'(export\s+default\s+|module\.exports\s*=)|//.*?$|/\*.*?\*/', '', content, flags=re.MULTILINE|re.DOTALL)
                config = json.loads(re.search(r'(\{[\s\S]*\})', content).group(1))
            return config.get(config_key) if config_key else config
        except:
            return None

    def isVideoFormat(self, url):
        return bool(re.search(r"(?i)\.(?:mp4|m3u8|flv|mkv|avi|ts|mov|mpd|m4a|wmv)(?:\?.*)?$", str(url)))

    def manualVideoCheck(self):
        return False

    @staticmethod
    def _varint(value):
        value = int(value)
        out = bytearray()
        while value > 0x7f:
            out.append((value & 0x7f) | 0x80)
            value >>= 7
        out.append(value)
        return bytes(out)

    @classmethod
    def _pb_int(cls, field, value):
        return cls._varint(field << 3) + cls._varint(value)

    @classmethod
    def _pb_bytes(cls, field, value):
        if isinstance(value, str):
            value = value.encode("utf-8")
        return cls._varint((field << 3) | 2) + cls._varint(len(value)) + value

    @staticmethod
    def _read_varint(data, pos):
        value = 0
        shift = 0
        while pos < len(data):
            b = data[pos]
            pos += 1
            value |= (b & 0x7f) << shift
            if not b & 0x80:
                return value, pos
            shift += 7
        raise ValueError("bad protobuf varint")

    @classmethod
    def _pb_parse(cls, data):
        fields = {}
        pos = 0
        while pos < len(data):
            key, pos = cls._read_varint(data, pos)
            field, wire = key >> 3, key & 7
            if wire == 0:
                value, pos = cls._read_varint(data, pos)
            elif wire == 1:
                value = data[pos:pos + 8]
                pos += 8
            elif wire == 2:
                size, pos = cls._read_varint(data, pos)
                value = data[pos:pos + size]
                pos += size
            elif wire == 5:
                value = data[pos:pos + 4]
                pos += 4
            else:
                raise ValueError("unsupported protobuf wire type: %s" % wire)
            fields.setdefault(field, []).append(value)
        return fields

    @staticmethod
    def _first(fields, number, default=b""):
        values = fields.get(number)
        return values[0] if values else default

    @staticmethod
    def _text(value):
        if isinstance(value, bytes):
            return value.decode("utf-8", "ignore")
        return str(value or "")

    @staticmethod
    def _random(length):
        chars = "1234567890ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
        return "".join(random.choice(chars) for _ in range(max(0, length - 1))) + "="

    @staticmethod
    def _check_crypto():
        if AES is None or RSA is None:
            raise RuntimeError("缺少 pycryptodome")

    @classmethod
    def _aes_encrypt_ecb(cls, text, key):
        cls._check_crypto()
        cipher = AES.new(key.encode("utf-8"), AES.MODE_ECB)
        return base64.b64encode(cipher.encrypt(pad(text.encode("utf-8"), AES.block_size))).decode("utf-8")

    @classmethod
    def _aes_decrypt_ecb(cls, text, key):
        cls._check_crypto()
        raw = base64.b64decode(text)
        cipher = AES.new(key.encode("utf-8"), AES.MODE_ECB)
        return unpad(cipher.decrypt(raw), AES.block_size).decode("utf-8", "ignore")

    @classmethod
    def _aes_encrypt_cbc_hex(cls, text, key):
        cls._check_crypto()
        key_b = key.encode("utf-8")
        cipher = AES.new(key_b, AES.MODE_CBC, iv=key_b)
        return cipher.encrypt(pad(text.encode("utf-8"), AES.block_size)).hex()

    @classmethod
    def _rsa_encrypt(cls, text, public_key_b64):
        cls._check_crypto()
        der = base64.b64decode(public_key_b64)
        key = RSA.import_key(der)
        return base64.b64encode(PKCS1_v1_5.new(key).encrypt(text.encode("utf-8"))).decode("utf-8")

    def _device(self):
        uid = uuid.uuid4().hex.upper()
        return {
            "country": "CN", "vName": self.version, "cpuId": "MT6893Z%2FCZA", "young": 0,
            "facturer": "Xiaomi", "pkg": self.cfg.get("pkg", ""), "uuid": uid,
            "resolution": "1080x2272", "mac": "02%3A00%3A00%3A00%3A00%3A00", "abid": "397",
            "model": "M2012K11AC", "plat": "android", "udid": uid, "dpi": "440", "net": "1",
            "lang": "zh", "brand": "Xiaomi", "density": "2.75", "appName": self.cfg.get("appName", "橘汁"),
            "cpu": "arm64-v8a", "chid": "10000", "carrier": "%E8%81%94%E9%80%9A",
            "_vOsCode": 30, "vOs": "11", "v": 1, "tenantId": "",
            "vApp": self.version.replace(".", ""), "device": 0, "androidID": uid.lower()[:16]
        }

    def _public_headers(self, protobuf=True):
        key = self.dynamic_key or self.public_key
        device = self._device()
        timestamp = int(time.time() * 1000)
        random_str = self._random(16)
        vapp = device.get("vApp") or "3019"
        device["sig"] = self._rsa_encrypt(str(timestamp) + random_str + vapp, key)
        device["random_str"] = random_str
        device["timestamp"] = timestamp
        sig23 = self._aes_encrypt_ecb(str(timestamp) + random_str, self.data_iv)
        device["sig2"] = sig23[:8]
        device["sig3"] = sig23[8:]
        params = self._aes_encrypt_cbc_hex(json.dumps(device, ensure_ascii=False, separators=(",", ":")), self.common_key)
        ctype = "application/x-protobuf" if protobuf else "application/json; charset=utf-8"
        accept = "application/x-protobuf" if protobuf else "application/json"
        return {
            "User-Agent": "okhttp/3.12.1", "Accept": accept, "Content-Type": ctype,
            "publicParams": json.dumps({"paramsData": params}, ensure_ascii=False, separators=(",", ":"))
        }

    def _secure_body(self, params):
        timestamp = int(time.time() * 1000)
        random8 = self._random(8)
        fake20 = self._random(20)
        query = "&".join("%s=%s" % (k, v) for k, v in params.items() if v is not None and str(v) != "")
        encrypted = random8 + self._aes_encrypt_ecb(query + str(timestamp), self.data_key)
        return b"".join([
            self._pb_bytes(1, encrypted[:20]), self._pb_bytes(2, encrypted[20:]),
            self._pb_bytes(3, fake20), self._pb_int(4, timestamp), self._pb_bytes(5, random8)
        ])

    def _post(self, path, body):
        if not self.session or not self.host:
            raise RuntimeError("接口域名获取失败")
        r = self.session.post(self.host + path, data=body, headers=self._public_headers(True), timeout=18)
        r.raise_for_status()
        return r.content

    def _get_json(self, path):
        if not self.session or not self.host:
            raise RuntimeError("接口域名获取失败")
        r = self.session.get(self.host + path, headers=self._public_headers(False), timeout=18)
        r.raise_for_status()
        return r.json()

    def _api_data(self, raw):
        return self._first(self._pb_parse(raw), 3, b"")

    def _load_dynamic_key(self):
        timestamp = int(time.time() * 1000)
        random_str = self._random(16)
        sign = self._rsa_encrypt(str(timestamp) + random_str, self.public_key)
        body = b"".join([
            self._pb_int(1, timestamp), self._pb_bytes(2, sign), self._pb_bytes(3, self._random(16)),
            self._pb_bytes(4, random_str), self._pb_bytes(5, self._random(16))
        ])
        data = self._api_data(self._post("/api/v5/find/app/zone", body))
        f = self._pb_parse(data)
        self.dynamic_key = "".join(self._text(self._first(f, n)) for n in (2, 3, 4, 5))

    def _parse_cover(self, raw):
        f = self._pb_parse(raw)
        return {"path": self._text(self._first(f, 1)), "thumb": self._text(self._first(f, 2))}

    def _parse_drama(self, raw):
        f = self._pb_parse(raw)
        cover = self._parse_cover(self._first(f, 2, b"")) if self._first(f, 2, b"") else {}
        return {
            "vod_id": str(self._first(f, 3, 0)), "vod_name": self._text(self._first(f, 5)),
            "vod_pic": cover.get("thumb") or cover.get("path", ""), "vod_remarks": self._text(self._first(f, 13)),
            "vod_year": str(self._first(f, 14, "")), "vod_area": self._text(self._first(f, 1))
        }

    def _parse_drama_page(self, raw):
        page = self._pb_parse(self._api_data(raw))
        return [self._parse_drama(v) for v in page.get(1, [])]

    def _parse_video(self, raw):
        f = self._pb_parse(raw)
        return {
            "title": self._text(self._first(f, 2)), "path": self._text(self._first(f, 4)),
            "source": self._text(self._first(f, 9)), "source_cn": self._text(self._first(f, 10))
        }

    def _is_match_line(self, line_name, keyword):
        name = line_name.strip().lower()
        key = keyword.strip()
        try:
            if key.startswith('/') and key.endswith('/'):
                return bool(re.search(key[1:-1], name, re.IGNORECASE))
        except:
            pass
        return key.lower() in name

    def _sort_and_filter_lines(self, lines):
        if not lines:
            return lines
        if self.line_block:
            filtered = [l for l in lines if not any(self._is_match_line(l['name'], kw) for kw in self.line_block)]
            lines = filtered
        if self.line_order:
            sorted_lines = []
            remaining = lines[:]
            for keyword in self.line_order:
                matched, unmatched = [], []
                for line in remaining:
                    (matched if self._is_match_line(line['name'], keyword) else unmatched).append(line)
                sorted_lines.extend(matched)
                remaining = unmatched
            lines = sorted_lines + remaining
        return lines

    def homeContent(self, filter):
        try:
            obj = self._get_json("/api/v3/drama/getCategory?orderBy=type_id")
            classes = []
            for item in obj.get("data") or []:
                if str(item.get("name", "")) == "公告":
                    continue
                tid, name = str(item.get("id", "")), str(item.get("name", ""))
                if not tid:
                    continue
                classes.append({"type_id": tid, "type_name": name})
            return {"class": classes}
        except:
            return {"class": []}

    def homeVideoContent(self):
        try:
            obj = self._get_json("/api/ex/v3/security/tag/list")
            data = obj.get("data", "")
            if data and isinstance(data, str):
                stripped = data.strip()
                if stripped and stripped[0] not in ('[', '{'):
                    data = self._aes_decrypt_ecb(data, self.data_key)
                    data = self._aes_decrypt_ecb(data, self.data_iv)
            arr = json.loads(data) if isinstance(data, str) else data
            videos = []
            for block in arr or []:
                for section in block.get("sections") or []:
                    for vod in section.get("vodList") or []:
                        pic = (vod.get("coverImage") or {}).get("path", "")
                        videos.append({"vod_id": str(vod.get("id", "")), "vod_name": vod.get("name", ""), "vod_pic": pic, "vod_remarks": vod.get("remark", "")})
            return {"list": videos}
        except:
            return {"list": []}

    def categoryContent(self, tid, pg, filter, extend):
        params = {
            "pagesize": "21", 
            "typeId1": str(tid), 
            "page": str(pg),
            "vodOrderBy": (extend or {}).get("排序", "最新"),
            "vodArea": (extend or {}).get("地区", ""), 
            "vodLang": (extend or {}).get("语言", ""),
            "vodClass": (extend or {}).get("类型", ""), 
            "vodYear": (extend or {}).get("年份", "")
        }
        try:
            raw = self._post("/api/proto/v5/drama/category", self._secure_body(params))
            f = self._pb_parse(self._api_data(raw))
            dramas = []
            for item in f.get(1, []):
                if not isinstance(item, bytes):
                    continue
                df = self._pb_parse(item)
                pic = ""
                cover_raw = self._first(df, 2, b"")
                if cover_raw:
                    cf = self._pb_parse(cover_raw)
                    for vals in cf.values():
                        for v in vals:
                            t = self._text(v)
                            t = re.sub(r'^[^h]*', '', t)
                            if t.startswith('http'):
                                pic = t
                                break
                        if pic:
                            break
                dramas.append({
                    "vod_id": str(self._first(df, 3, 0)),
                    "vod_name": self._text(self._first(df, 5)),
                    "vod_pic": pic,
                    "vod_remarks": self._text(self._first(df, 13))
                })
            return {"list": dramas, "page": int(pg), "pagecount": 9999, "limit": 21, "total": 9999}
        except:
            return {"list": [], "page": int(pg or 1), "pagecount": 0, "limit": 21, "total": 0}

    def detailContent(self, ids):
        try:
            raw = self._post("/api/proto/v5/drama/getDetail", self._secure_body({"id": str(ids[0])}))
            f = self._pb_parse(self._api_data(raw))
            cover_raw = self._first(f, 2, b"")
            cover = self._parse_cover(cover_raw) if cover_raw else {}
            sources = {}
            for item in f.get(29, []):
                video = self._parse_video(item)
                quality = video.get("source_cn", "") or video.get("source", "") or "未知"
                source = video.get("source", "") or ""
                line_name = f"{quality} ({source})" if source and quality != source else quality
                path = video["path"]
                if not self.isVideoFormat(path):
                    token = base64.b64encode(json.dumps({"vodPlayFrom": video["source"], "playUrl": path}, ensure_ascii=False, separators=(",", ":")).encode()).decode()
                else:
                    token = path
                sources.setdefault(line_name, []).append((video["title"] or "播放") + "$" + token)
            
            lines = [{"name": name, "urls": urls} for name, urls in sources.items()]
            lines = self._sort_and_filter_lines(lines)
            play_from = "$$$".join([line["name"] for line in lines])
            play_url = "$$$".join(["#".join(line["urls"]) for line in lines])
            
            vod = {
                "vod_id": str(ids[0]), "vod_name": self._text(self._first(f, 9)),
                "vod_pic": cover.get("path") or cover.get("thumb", ""),
                "vod_actor": self._text(self._first(f, 25)), "vod_director": self._text(self._first(f, 12)),
                "vod_area": self._text(self._first(f, 1)), "vod_year": str(self._first(f, 18, "")),
                "vod_remarks": self._text(self._first(f, 26)), "vod_content": self._text(self._first(f, 6)),
                "vod_play_from": play_from, "vod_play_url": play_url
            }
            return {"list": [vod]}
        except:
            return {"list": []}

    def searchContent(self, key, quick, pg="1"):
        try:
            raw = self._post("/api/proto/v5/drama/search", self._secure_body({"searchKeys": key, "page": str(pg), "pagesize": "21"}))
            results = self._parse_drama_page(raw)
            # 只取第一个搜索结果，确保精准匹配
            if results:
                return {"list": [results[0]]}
            return {"list": []}
        except:
            return {"list": []}

    def playerContent(self, flag, id, vipFlags):
        try:
            if self.isVideoFormat(id):
                return {"parse": 0, "url": id, "header": {}}
            params = json.loads(base64.b64decode(id).decode("utf-8"))
            raw = self._post("/api/proto/v5/videoUsableUrl", self._secure_body(params))
            f = self._pb_parse(self._api_data(raw))
            headers = {}
            for entry in f.get(6, []):
                ef = self._pb_parse(entry)
                k, v = self._text(self._first(ef, 1)), self._text(self._first(ef, 2))
                if k:
                    headers[k] = v
            return {"parse": 0, "url": self._text(self._first(f, 1)), "header": headers}
        except:
            return {"parse": 1, "url": id, "header": {}}

    def localProxy(self, param):
        return [404, "text/plain", "", None]

    def destroy(self):
        if self.session:
            try:
                self.session.close()
            except:
                pass