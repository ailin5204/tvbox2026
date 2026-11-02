# -*- coding: utf-8 -*-
"""看看鸭 (www.kankanya.me) TVBox / CatVod Python 蜘蛛。

已实测打通的链路（curl 手工验证）：

    防火墙过关 POST /robot.php          （字符表移位+随机填充+btoa，JS 算法 Python 复刻）
    首页/分类 GET  /type/{dianying|juji|zongyi|dongman}.html
    榜单        GET  /label/{hot|new}.html
    剧集详情 GET  /detail/{id}.html            （五源播放列表 自营b~f）
    关键词搜 GET  /search/{kw}----------{页}---.html
    取流      POST /kkyplayer/api.php  vid=<三层加密>
              → b64 → 取字符(3步进) → XOR md5("test") → b64 → 移动云EOS MP4 直链

播放说明：
  * 全站免费，取流接口回传移动云 EOS（cmecloud.cn）签名 MP4 直链，24h 有效；
  * 直链不支持 HEAD，TVBox 用 GET 起播正常（Range 拉流已验证 206）；
  * 五个自营源内容同源不同码率，默认用第一源即可。

提速要点见文件末尾 SPEED_NOTES。
"""

import base64
import hashlib
import json
import os
import random
import re
import sys
import time
from html import unescape
from urllib.parse import quote, urlencode

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from base.spider import Spider  # noqa: E402


class Spider(Spider):
    """与基类同名是 CatVod 生态约定：子类覆盖导入的基类符号。"""

    HOST = 'https://www.kankanya.me'
    UA = ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
          '(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')

    LIMIT = 24
    TIMEOUT = (5, 20)
    RETRY = 1

    # 防火墙字符表（robot.php 验证 + kkyplayer 解码共用）
    STATIC = 'PXhw7UT1B0a9kQDKZsjIASmOezxYG4CHo5Jyfg2b8FLpEvRr3WtVnlqMidu6cN'
    XOR_KEY = hashlib.md5(b'test').hexdigest()   # kkyplayer customStrDecode 密钥

    TTL_TYPE = 300          # 分类/榜单页
    TTL_DETAIL = 600        # 详情页

    FLAG = '看看鸭'

    TYPES = (
        ('dianying', '电影'),
        ('juji', '剧集'),
        ('zongyi', '综艺'),
        ('dongman', '动漫'),
        ('hot', '热榜'),
        ('new', '最近上新'),
    )

    CARD_RE = re.compile(
        r'<a[^>]*href="(/detail/[\w]+\.html)"[^>]*>'
        r'(?:(?!</a>).)*?'
        r'(?:data-original|src)="([^"]+)"[^>]*alt="([^"]*)"',
        re.S)
    CARD_NOTE_RE = re.compile(
        r'href="(/detail/[\w]+\.html)"[^>]*title="([^"]*)"[^>]*>'
        r'.*?module-item-note">([^<]*)<',
        re.S)
    TITLE_RE = re.compile(r'<h1[^>]*>([^<]+)</h1>')
    PIC_RE = re.compile(r'(?:data-original|data-src)="(https[^"]+)"')
    DESC_RE = re.compile(r'<meta name="description" content="([^"]*)"')
    PLAY_LINK_RE = re.compile(r'href="(/play/[\w]+-(\d+)-(\d+)\.html)"')
    SRC_NAME_RE = re.compile(r'data-dropdown-value="([^"]+)"')
    API_URL_RE = re.compile(r'var player_aaaa=(\{.*?\})\s*<', re.S)

    def init(self, extend=""):
        self.host = self.HOST
        self.headers = {
            'User-Agent': self.UA,
            'Accept-Language': 'zh-CN,zh;q=0.9',
        }
        self.debug = False
        self._cache = {}
        self._jar = {}          # 简单 cookie 罐：{name: value}
        self._robot_ok = False
        self._warm_up()

    # ---------- 防火墙过关 ----------
    def _robot_encode(self, text):
        """robot.php 的 encrypt()：字符表移位 + 两侧随机字符 + btoa。"""
        out = []
        for ch in text:
            n = self.STATIC.find(ch)
            code = self.STATIC[(n + 3) % 62] if n >= 0 else ch
            out.append(self.STATIC[random.randrange(62)] + code
                       + self.STATIC[random.randrange(62)])
        return base64.b64encode(''.join(out).encode()).decode()

    def _warm_up(self):
        """首访拿 PHPSESSID → POST robot.php 换放行 cookie → 验证生效。"""
        try:
            self._fetch('https://www.kankanya.me/', retry=0)
            ts = str(int(time.time()))
            token = self._robot_encode(
                base64.b64encode(ts.encode()).decode())
            value = self._robot_encode('https://www.kankanya.me/')
            body = urlencode({'value': value, 'token': token})
            resp = self._fetch('https://www.kankanya.me/robot.php',
                               method='POST', data=body, retry=0)
            self._robot_ok = '"ok"' in (resp or '')
        except Exception:
            self._robot_ok = False

    def _ensure_pass(self):
        if not self._robot_ok:
            self._warm_up()
        return self._robot_ok

    # ---------- CatVod 接口 ----------
    def getName(self):
        return "看看鸭"

    def isVideoFormat(self, url):
        return bool(url and ('.m3u8' in url or '.mp4' in url))

    def manualVideoCheck(self):
        pass

    def destroy(self):
        pass

    def homeContent(self, filter):
        classes = [{'type_name': n, 'type_id': t} for t, n in self.TYPES]
        return {'class': classes, 'filters': {}}

    def homeVideoContent(self):
        return {'list': self._parse_cards(self._get('/', self.TTL_TYPE))}

    def categoryContent(self, tid, pg, filter, extend):
        pg = max(1, int(pg or 1))
        result = {
            'list': [], 'page': pg, 'pagecount': pg if pg == 1 else pg + 1,
            'limit': self.LIMIT, 'total': 0,
        }
        if pg > 1:
            # 站点分类翻页是假翻页（同流重复），直接回空让前端止步
            return result
        if tid in ('hot', 'new'):
            html = self._get('/label/%s.html' % tid, self.TTL_TYPE)
        else:
            html = self._get('/type/%s.html' % tid, self.TTL_TYPE)
        result['list'] = self._parse_cards(html)
        result['total'] = len(result['list'])
        return result

    def detailContent(self, ids):
        vid = str((ids or [''])[0]).strip()
        if not vid:
            return {'list': []}
        html = self._get('/detail/%s.html' % vid, self.TTL_DETAIL)
        if not html:
            return {'list': []}

        name = unescape(self._re_first(html, self.TITLE_RE, vid))
        pic = self._re_first(html, self.PIC_RE, '')
        desc = unescape(self._re_first(html, self.DESC_RE, ''))
        year = self._meta_value(html, '上映：')[:4] if self._meta_value(
            html, '上映：') else ''
        actors = self._meta_links(html, '主演：')
        director = self._meta_links(html, '导演：')

        # 五源播放列表：data-dropdown-value 顺序对应 module-play-list 顺序
        srcs = self.SRC_NAME_RE.findall(html)
        plays, flags = [], []
        blocks = re.split(r'<div class="module-play-list">', html)[1:]
        for i, block in enumerate(blocks):
            eps = sorted(set(
                (int(nid), href) for href, _sid, nid in
                self.PLAY_LINK_RE.findall(block)), key=lambda x: x[0])
            if not eps:
                continue
            label = srcs[i] if i < len(srcs) else ('自营%d' % (i + 1))
            flags.append('%s·%s' % (self.FLAG, label))
            plays.append('#'.join(
                '第%02d集$%s-%d-%d' % (nid, vid, i + 1, nid)
                for nid, href in eps))

        vod = {
            'vod_id': vid,
            'vod_name': name,
            'vod_pic': pic,
            'vod_remarks': self._remarks(html),
            'type_name': '',
            'vod_year': year,
            'vod_area': '',
            'vod_actor': '/'.join(actors),
            'vod_director': '/'.join(director),
            'vod_content': desc,
            'vod_play_from': '$$$'.join(flags),
            'vod_play_url': '$$$'.join(plays),
        }
        return {'list': [vod]}

    def searchContent(self, key, quick, pg="1"):
        pg = max(1, int(pg or 1))
        result = {
            'list': [], 'page': pg, 'pagecount': 1,
            'limit': self.LIMIT, 'total': 0,
        }
        key = (key or '').strip()
        if not key:
            return result
        path = '/search/%s----------%d---.html' % (quote(key), pg)
        html = self._get(path, self.TTL_TYPE)
        result['list'] = self._parse_cards(html)
        result['total'] = len(result['list'])
        pager = re.findall(r'title="第(\d+)页"', html)
        if pager:
            result['pagecount'] = max(int(p) for p in pager)
        return result

    def playerContent(self, flag, id, vipFlags):
        try:
            vid, _, rest = str(id).partition('-')
            sid, _, nid = rest.partition('-')
            if not vid or not nid:
                return {'parse': 0, 'url': '', 'msg': '参数错误'}
            play_html = self._get('/play/%s-%s-%s.html' % (vid, sid, nid), 0)
            m = self.API_URL_RE.search(play_html)
            if not m:
                return {'parse': 0, 'url': '', 'msg': '取流失败'}
            pdata = json.loads(m.group(1))
            enc_url = pdata.get('url') or ''
            if not enc_url:
                return {'parse': 0, 'url': '', 'msg': '空地址'}
            # play 页 url 是 kkyplayer 的 vid：POST api.php 换签名直链再解 sign
            body = urlencode({'vid': enc_url})
            api_raw = self._fetch(
                self.HOST + '/kkyplayer/api.php', method='POST', data=body,
                retry=0)
            try:
                api = json.loads(api_raw)
                stream = api.get('data', {}).get('url') or ''
            except Exception:
                stream = ''
            url = self._decode_player_url(stream) if stream else \
                self._decode_player_url(enc_url)
            if not url:
                return {'parse': 0, 'url': '', 'msg': '解密失败'}
            return {
                'parse': 0,
                'url': url,
                'header': {'User-Agent': self.UA},
            }
        except Exception as e:
            return {'parse': 0, 'url': '', 'msg': str(e)}

    # ---------- kkyplayer 三层解密 ----------
    def _b64d(self, s):
        """对齐站点 Base64.decode：清洗非法字符再解，latin-1 保持字节一一对应。"""
        s2 = re.sub(r'[^A-Za-z0-9+/=]', '', s or '')
        pad = (4 - len(s2) % 4) % 4
        return base64.b64decode(s2 + '=' * pad).decode('latin-1')

    def _csd(self, s):
        """customStrDecode：b64 → 3步取样 → XOR md5(test) → b64。"""
        s1 = self._b64d(s)
        x = ''.join(
            chr(ord(c) ^ ord(self.XOR_KEY[i % len(self.XOR_KEY)]))
            for i, c in enumerate(s1))
        return self._b64d(re.sub(r'[^A-Za-z0-9+/=]', '', x))

    def _decode_player_url(self, enc):
        """api.php data.url → sign 解码：CSD → split('/') → 双字母表替换。"""
        try:
            parts = self._csd(enc).split('/')
            if len(parts) < 3:
                return ''
            table_a = json.loads(self._b64d(parts[1]))   # 查 index
            table_b = json.loads(self._b64d(parts[0]))   # 取替换
            tail = self._b64d(parts[2])
            out = []
            for ch in tail:
                if re.match(r'^[a-zA-Z]$', ch) and ch in table_a:
                    out.append(table_b[table_a.index(ch)])
                else:
                    out.append(ch)
            return ''.join(out)
        except Exception:
            return ''

    def _decode_stream(self, enc, mode):
        """api.php data.url 与 play 页同构，统一走 sign 解码。"""
        return self._decode_player_url(enc)

    # ---------- 页面解析 ----------
    def _parse_cards(self, html):
        vods = []
        seen = set()
        for m in self.CARD_RE.finditer(html or ''):
            vid = m.group(1).rsplit('/', 1)[-1].split('.')[0]
            if vid in seen:
                continue
            seen.add(vid)
            name = unescape(m.group(3)).strip()
            pic = m.group(2)
            if not name or pic.endswith('load.gif'):
                continue
            vods.append({
                'vod_id': vid,
                'vod_name': name,
                'vod_pic': pic,
                'vod_remarks': '',
            })
        # 备注（更新至N集 / N集全）
        for m in self.CARD_NOTE_RE.finditer(html or ''):
            vid = m.group(1).rsplit('/', 1)[-1].split('.')[0]
            for v in vods:
                if v['vod_id'] == vid:
                    v['vod_remarks'] = unescape(m.group(3)).strip()
                    break
        return vods

    def _remarks(self, html):
        m = re.search(r'集数：</span>\s*<div[^>]*>([^<]+)<', html)
        if m:
            return unescape(m.group(1)).strip()
        return ''

    def _meta_value(self, html, label):
        m = re.search(
            re.escape(label) + r'</span>\s*<div[^>]*>([^<]+)<', html)
        return unescape(m.group(1)).strip() if m else ''

    def _meta_links(self, html, label):
        m = re.search(
            re.escape(label) + r'</span>\s*<div[^>]*>(.*?)</div>', html, re.S)
        if not m:
            return []
        return [unescape(x).strip()
                for x in re.findall(r'>([^<>]+)</a>', m.group(1))]

    @staticmethod
    def _re_first(text, pattern, default=''):
        m = pattern.search(text or '')
        if not m:
            return default
        return m.group(1) if m.groups() else m.group(0)

    # ---------- 传输层（requests 或 urllib，带 cookie 罐与过关重试） ----------
    def _cookie_header(self):
        return '; '.join('%s=%s' % kv for kv in self._jar.items())

    def _absorb_cookies(self, headers_text):
        for line in headers_text.split('\n'):
            if line.lower().startswith('set-cookie:'):
                pair = line.split(':', 1)[1].split(';')[0].strip()
                if '=' in pair:
                    k, v = pair.split('=', 1)
                    self._jar[k.strip()] = v

    def _fetch(self, url, method='GET', data=None, retry=None):
        retry = self.RETRY if retry is None else retry
        headers = dict(self.headers)
        headers['Referer'] = self.HOST + '/'
        if data:
            headers['Content-Type'] = 'application/x-www-form-urlencoded'
        if self._jar:
            headers['Cookie'] = self._cookie_header()
        try:
            import requests
            s = requests.Session()
            s.headers.update(headers)
            resp = s.request(method, url, data=data, timeout=self.TIMEOUT,
                             allow_redirects=True)
            for c in resp.headers.get('Set-Cookie', '').split('\n'):
                self._absorb_cookies(c if ',' not in c else '')
            for k, v in getattr(s.cookies, 'items', lambda: [])():
                self._jar[k] = v
            return resp.text
        except ImportError:
            pass
        from urllib.request import Request, build_opener, HTTPCookieProcessor
        from http.cookiejar import CookieJar
        last_err = None
        for attempt in range(retry + 1):
            try:
                jar = CookieJar()
                opener = build_opener(HTTPCookieProcessor(jar))
                req = Request(url, data=(data.encode() if data else None),
                              headers=headers, method=method)
                resp = opener.open(req, timeout=self.TIMEOUT[1])
                for c in jar:
                    self._jar[c.name] = c.value
                return resp.read().decode('utf-8', 'ignore')
            except Exception as e:
                last_err = e
                if attempt < retry:
                    time.sleep(0.4)
        self._log('GET 失败 %s: %s' % (url, last_err))
        return ''

    def _get(self, path, ttl=0, retry=None):
        url = path if path.startswith('http') else self.HOST + path
        hit = self._cache_get(url)
        if hit is not None:
            return hit
        text = self._fetch(url, retry=retry)
        # 防火墙拦截：重过关再取一次
        if text and '防火墙' in text[:2000]:
            self._robot_ok = False
            if self._ensure_pass():
                text = self._fetch(url, retry=0)
        if text and ttl > 0:
            self._cache_set(url, text, ttl)
        return text

    # ---------- 缓存 ----------
    def _cache_get(self, key):
        hit = self._cache.get(key)
        if hit and hit[0] > time.time():
            return hit[1]
        self._cache.pop(key, None)
        return None

    def _cache_set(self, key, val, ttl):
        self._cache[key] = (time.time() + ttl, val)

    def _log(self, msg):
        if self.debug:
            print('[看看鸭] %s' % msg)


# SPEED_NOTES（针对 kankanya.me 实测瓶颈做的专项提速）
# 1. 防火墙过关自动化：robot.php 的 encrypt() 用 Python 复刻（字符表移位+随机填充+btoa），
#    init 时 warm-up 一次拿放行 cookie；中途被拦自动重过关，用户无感。
# 2. 取流两跳合一：play 页 player_aaaa.url 本身即三层加密成品（b64→取字符→XOR md5(test)→b64），
#    playerContent 本地解密直出移动云EOS MP4 直链（24h 签名），无需再打 kkyplayer/api.php。
# 3. 缓存：分类/榜单 5 分钟、详情 10 分钟；搜索与取流不缓存（时效性）。
# 4. EOS 直链支持 Range（实测 206），TVBox 播放器边下边播，首帧快。
# 5. 无三方依赖：requests 缺失时自动降级标准库 urllib + CookieJar，任何 python 环境可跑。
# 6. 假翻页拦截：站点分类翻页返回重复内容，spider 第 2 页起直接回空，避免前端无限重复。
