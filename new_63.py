# -*- coding: utf-8 -*-
"""
饭搭子影视 (fdzys.com) Python Spider — 兼容 FongMi/TV (T3) 与 WebHomeTV / PeekPro (T4)
站点: https://fdzys.com/  (米宅 MizhiADY 模板 · 苹果CMS V10)

特性:
  - 纯 HTML/SSR 抓取,无 XHR 依赖,无 Playwright,启动即可用
  - 分类路由用拼音 slug(/movie/dongzuo 等),二/三级子分类内置
  - 详情页通过 window.player_xxxx 全局变量解析多线路
  - 三档播放优先级:直链 m3u8/mp4 > 解析器直跳 > 官源交壳子嗅探
  - 搜索 + 分类浏览 + 首页推荐全链路
  - 内存缓存首页/分类(60s)、详情(5min),大幅减少重复请求
  - 全局 HTTP 连接复用,短超时,SSL 禁验证
"""

import sys
import re
import json
import time
import ssl
import gzip
import io
import threading
import urllib.request
import urllib.parse
import urllib.error
import http.client
from http.client import HTTPException

sys.path.append('..')

# ===== 兼容导入 =====
# 真实壳子里 base.spider.Spider 提供 fetch(url, headers=..., timeout=...) 入口
# 离线/单测时 fallback 到 stdlib urllib 实现

# 共享 SSL context(所有 fetch 复用,加速连接)
_SHARED_SSL_CTX = ssl.create_default_context()
_SHARED_SSL_CTX.check_hostname = False
_SHARED_SSL_CTX.verify_mode = ssl.CERT_NONE


# 每线程独立连接池:同 host 保持 keep-alive,复用 TCP/TLS,避免每次握手 → 大幅提速
_conn_pool_local = threading.local()

def _pooled_conn(url, timeout):
    """返回 (connection, parsed_url),连接按 (scheme,host,port) 存线程池"""
    p = urllib.parse.urlparse(url)
    key = p.scheme + '://' + p.netloc
    conn = getattr(_conn_pool_local, key, None)
    if conn is None:
        cls = http.client.HTTPSConnection if p.scheme == 'https' else http.client.HTTPConnection
        conn = cls(p.netloc, timeout=timeout, context=_SHARED_SSL_CTX)
        setattr(_conn_pool_local, key, conn)
    return conn, p

def _stdlib_fetch(url, headers=None, **kw):
    """连接池版 fetch: 同 host 复用 keep-alive 连接 + gzip / SSL 跳过;失败自动重建重试一次"""
    import types as _types
    timeout = kw.pop('timeout', 15)
    hdrs = {'Connection': 'keep-alive'}
    if headers:
        hdrs.update({k: v for k, v in headers.items() if k.lower() != 'host'})
        if not any(k.lower() == 'connection' for k in headers):
            pass  # keep-alive 已设
    conn, p = _pooled_conn(url, timeout)
    path = p.path or '/'
    if p.query:
        path += '?' + p.query
    last_err = None
    for _ in (0, 1):
        try:
            conn.request('GET', path, headers=hdrs)
            r = conn.getresponse()
            data = r.read()
            enc = (r.getheader('Content-Encoding') or '').lower()
            if enc == 'gzip':
                data = gzip.decompress(data)
            return _types.SimpleNamespace(text=data.decode('utf-8', 'ignore'), content=data)
        except Exception as e:
            last_err = e
            try: conn.close()
            except Exception: pass
            try: _conn_pool_local.__dict__.pop(p.scheme + '://' + p.netloc, None)
            except Exception: pass
            conn, _ = _pooled_conn(url, timeout)
    return _types.SimpleNamespace(text='', content=b'', error=last_err)

try:
    from base.spider import Spider as _BaseSpider
    if not hasattr(_BaseSpider, 'fetch'):
        _BaseSpider.fetch = _stdlib_fetch
except ImportError:
    _BaseSpider = type('Spider', (), {'fetch': _stdlib_fetch})

# 模块级 fetch 工具:统一走 _stdlib_fetch(更稳,不依赖 self 继承)
def _fetch(url, headers=None, timeout=10):
    return _stdlib_fetch(url, headers=headers, timeout=timeout)


# ============================================================
# 常量
# ============================================================

HOST = "https://fdzys.com"
UA = "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36"

# 兜底解析器(官源时用,失败交给壳子)
FALLBACK_PARSER = "https://svip.qlplayer.cyou/?url={url}&autoplay=1"

# 站点 playerconfig.js 里的解析器映射(默认,运行时可被站点的实际配置覆盖)
# from 名称 -> 解析器 URL 模板(含 {url} 占位)
FALLBACK_PARSER_MAP = {
    "qq": "https://svip.qlplayer.cyou/?url={url}",
    "qiyi": "https://svip.qlplayer.cyou/?url={url}",
    "iqiyi": "https://svip.qlplayer.cyou/?url={url}",
    "youku": "https://svip.qlplayer.cyou/?url={url}",
    "mgtv": "https://svip.qlplayer.cyou/?url={url}",
    "bilibili": "https://svip.qlplayer.cyou/?url={url}",
    "1080zyk": "https://vip.zykbf.com/?url={url}",
    "hnm3u8": "https://www.hnjiexi.com/m3u8/?url={url}",
    "ffm3u8": "https://ffzyplayer.com/?url={url}",
    "wjm3u8": "https://svip.qlplayer.cyou/?url={url}",  # 无尽云
    "dplayer": "",   # 通常自带播放器,无解析
}

# ========== 一级分类 ==========
CLASSES = [
    {"type_name": "电影", "type_id": "movie"},
    {"type_name": "电视剧", "type_id": "tv"},
    {"type_name": "动漫", "type_id": "dongman"},
    {"type_name": "综艺", "type_id": "zongyi"},
    {"type_name": "体育", "type_id": "tiyu"},
    {"type_name": "短剧", "type_id": "duanju"},
]

# ========== 二级分类 ==========
# 三类筛选条件:类型(剧情/动作…) / 地区(大陆/美国…) / 年份(2024/2025…)
# mizhiady 模板把不同维度的筛选放在同层,slug 形如:
#   类型:  /movie/dongzuo, /movie/xiju, /movie/kongbu...
#   地区:  /movie/dalu, /movie/meiguo, /movie/rihan...
#   年份:  /movie/2024, /movie/2025, /movie/2026...
# 一个分类下会有几十甚至上百个 slug。运行时按需加载。

# 启动时只用"类型"作为默认筛选(用户从壳子点开能看到),其余维度做成
# "年份/地区"扩展,首次请求时按需补齐
SUBCATS_BASE = {
    # 以下 slug 均已对站内真实路径验证(2026-09-11),避免点击二级分类 404 空数据
    "movie": [
        {"n": "全部", "v": ""},
        {"n": "动作", "v": "dongzuo"},
        {"n": "喜剧", "v": "xiju"},
        {"n": "爱情", "v": "aiqing"},
        {"n": "科幻", "v": "kehuan"},
        {"n": "恐怖片", "v": "kongbupian"},
        {"n": "剧情", "v": "juqing"},
        {"n": "战争", "v": "zhanzheng"},
    ],
    "tv": [
        {"n": "全部", "v": ""},
        {"n": "国产剧", "v": "guochan"},
        {"n": "欧美剧", "v": "oumei"},
        {"n": "日本剧", "v": "riben"},
        {"n": "韩国剧", "v": "hanguo"},
    ],
    "dongman": [
        {"n": "全部", "v": ""},
        {"n": "国漫", "v": "guochan"},
        {"n": "日韩", "v": "rihan"},
        {"n": "欧美", "v": "oumei"},
        {"n": "港台", "v": "gangtai"},
        {"n": "海外", "v": "haiwai"},
    ],
    "zongyi": [
        {"n": "全部", "v": ""},
        {"n": "大陆", "v": "dalu"},
        {"n": "港台", "v": "goutong"},
        {"n": "日韩", "v": "rihan"},
        {"n": "欧美", "v": "oumei"},
    ],
    "tiyu": [
        {"n": "全部", "v": ""},
        {"n": "足球", "v": "zuqiu"},
        {"n": "篮球", "v": "lanqiu"},
        {"n": "网球", "v": "wangqiu"},
        {"n": "斯诺克", "v": "taiqiu"},
    ],
    "duanju": [{"n": "全部", "v": ""}],
}

# 运行时缓存:每个 cat 的完整 slug 集合(含自动发现的年份/地区/类型)
SUBCATS = {k: list(v) for k, v in SUBCATS_BASE.items()}

# 构建 TVBox 用的筛选器
FILTERS = {}
for c in CLASSES:
    tid = c["type_id"]
    FILTERS[tid] = [
        {"key": "class", "name": "类型", "value": SUBCATS.get(tid, [{"n": "全部", "v": ""}])},
    ]


# ============================================================
# Spider 主类
# ============================================================

class Spider(_BaseSpider):

    def getName(self):
        return "饭搭子影视"

    # ===== 初始化 =====
    def init(self, extend=""):
        self.header = {
            "User-Agent": UA,
            "Referer": HOST + "/",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
        }

        # 内存缓存
        self._page_cache = {}      # url -> (text, expire_ts)
        self._home_cache = []      # 首页推荐卡片
        self._home_cache_time = 0
        self._cache_ttl = 60       # 列表 60s
        self._detail_ttl = 300     # 详情 5min
        self._req_timeout = 8
        # 已知子分类 slug(用于过滤分类页里的子分类按钮)
        # 先种入 SUBCATS 枚举,后续自动发现会扩充(同一 session 内)
        self._sub_slugs = {c["type_id"]: set() for c in CLASSES}
        for c in CLASSES:
            for s in SUBCATS.get(c["type_id"], []):
                if s.get('v'):
                    self._sub_slugs[c["type_id"]].add(s['v'])
        # 已知的"非视频" slug(辅助页 / 通用过滤)
        self._non_video_slugs = {'all', 'rank', 'search', 'gbook', 'history'}
        # 子分类全量缓存:每个 cat 完整 list(类型 + 地区 + 年份)
        self._subcat_loaded = set()  # 已抓过完整子分类的 cat
        # 复用的 SSL context(urllib 每次 new 太慢)
        self._ssl_ctx = ssl.create_default_context()
        self._ssl_ctx.check_hostname = False
        self._ssl_ctx.verify_mode = ssl.CERT_NONE
        # 站点的线路解析器映射(从 /static/js/playerconfig.js 拉)
        self._parser_map = FALLBACK_PARSER_MAP.copy()
        # 已知地区 slug 集合(用于 _discover_subcats)
        self._area_kw = {
            'dalu', 'guochan', 'xianggang', 'gangtai', 'taiwan', 'meiguo', 'oumei',
            'rihan', 'riben', 'hanguo', 'yingguo', 'faguo', 'deguo', 'jianada',
            'australia', 'xibanya', 'yidali', 'qita', 'minnanyu', 'guoyu', 'deyu',
            'fayu', 'riyu', 'hanyu', 'qitayu', 'taiguo', 'yindu', 'eluosi', 'aizhou',
        }
        # 预热:首次进 shell 时,后台预加载各分类的子分类(filter-li)
        # 让 homeContent 一返回就有完整筛选器,不延迟
        threading.Thread(target=self._warmup_subcats, daemon=True).start()

    # ===== 通用 GET(带缓存) =====
    def _http_get(self, url, timeout=None, use_cache=True, ttl=None):
        if use_cache and url in self._page_cache:
            text, exp = self._page_cache[url]
            if time.time() < exp:
                return text
        to = timeout or self._req_timeout
        try:
            rsp = _fetch(url, headers=self.header, timeout=to)
            text = rsp.text
            if use_cache and text and ttl:
                self._page_cache[url] = (text, time.time() + ttl)
            return text
        except Exception:
            return ""

    # ===== URL 工具 =====
    def _abs(self, path):
        if not path:
            return ""
        if path.startswith("http"):
            return path
        if path.startswith("//"):
            return "https:" + path
        if path.startswith("/"):
            return HOST + path
        return HOST + "/" + path

    def _classify_url(self, path):
        """统一通过 ?pg=N 控制分页,site 对应的真实分页可能是 ?page= / /page/N,做多尝试"""
        if not path:
            return path
        # 大部分 mizhiady 模板用 ?page=1
        sep = "&" if "?" in path else "?"
        return f"{path}{sep}page={{n}}"

    # ===== HTML 卡片解析 =====
    # mizhiady 模板实际卡片 HTML 结构(从真实页面枚举):
    #   顶部 banner  / 轮播:
    #     <a class="swiper-lazy" href="..." data-slide-bg="..." title="寻她"></a>
    #     <a class="play-btn" href="..." target="_blank">寻她</a>
    #   列表卡片:
    #     <a class="module-item" href="...">
    #       <div class="module-item-cover">
    #         <img data-src="poster.jpg" />
    #         <div class="module-item-text">HD国语</div>
    #       </div>
    #       <div class="module-item-title">寻她</div>
    #     </a>
    # 子分类(<a class="chip ...">): 不要, 内部无 title/img/poster
    _CARD_RE = re.compile(
        r'<a\b[^>]+href="(https?://[^"]*/[a-z]+/[a-z0-9\-]+|/[a-z]+/[a-z0-9\-]+)"[^>]*>(.*?)</a>',
        re.S | re.I
    )
    _TITLE_ATTR_RE = re.compile(r'\btitle\s*=\s*"([^"]+)"', re.I)
    _TITLE_TEXT_RE = re.compile(
        r'<(?:div|span|h\d)[^>]*class="[^"]*(?:title|name|module-item-title|vod-title)[^"]*"[^>]*>([^<]{1,60})</',
        re.S | re.I
    )
    # img 标签里的图:mizhiady 的 img 有 data-src(真实图) + src(1x1 占位),优先 data-src
    _IMG_RE = re.compile(
        r'<(?:img)\b[^>]*?\bdata-src\s*=\s*"([^"]+)"|<img\b[^>]*?\bsrc\s*=\s*"([^"]+)"',
        re.I
    )
    _PIC_ATTR_RE = re.compile(
        r'\bdata-(?:slide-bg|poster|original|src|lazy)\s*=\s*"([^"]+\.(?:jpg|jpeg|png|webp|gif)[^"]*)"',
        re.I
    )
    _REMARK_RE = re.compile(
        r'<(?:div|span)[^>]*class="[^"]*(?:remarks|tag|status|update|module-item-text|episode)[^"]*"[^>]*>([^<]{1,30})</',
        re.S | re.I
    )
    # 子分类/导航/筛选按钮(不要)
    _CHIP_OR_NAV_RE = re.compile(
        r'class\s*=\s*"[^"]*(?:chip|filter-li|filter_li|tab-item|tab_item|nav-link|nav_link|menu-?item|module-nav)[^"]*"',
        re.I
    )

    def _parse_cards(self, html, limit=60):
        """从分类页 HTML 解析出卡片列表

        mizhiady 实际结构:每个视频在 HTML 中出现 3-5 次(轮播、play-btn、content-card 等),
        我们按 vod_id(=path)聚合,合并所有 <a> 块的 title/图/文本。
        """
        if not html:
            return []

        from urllib.parse import urlparse
        # 一次扫描,按 path 聚合所有 <a> 块
        agg = {}  # path -> {"tags": [...], "titles": [...], "pics": [...], "texts": [...], "remarks": [...]}
        for m in self._CARD_RE.finditer(html):
            url = m.group(1)
            inner = m.group(2) or ""
            full_tag = m.group(0)
            if url.startswith("http"):
                path = urlparse(url).path
            else:
                path = url
            parts = [p for p in path.split('/') if p]
            if len(parts) != 2:
                continue
            cat, slug = parts
            if cat not in {"movie", "tv", "dongman", "zongyi", "tiyu", "duanju"}:
                continue
            if path not in agg:
                agg[path] = {"cat": cat, "slug": slug,
                             "tags": [], "titles": [], "pics": [], "texts": [], "remarks": []}
            a = agg[path]
            a["tags"].append(full_tag)
            # title 属性
            tm = self._TITLE_ATTR_RE.search(full_tag)
            if tm and tm.group(1).strip():
                a["titles"].append(tm.group(1).strip())
            # 内部 .title / .name 文字
            tm = self._TITLE_TEXT_RE.search(inner)
            if tm and tm.group(1).strip():
                a["titles"].append(tm.group(1).strip())
            # 内部纯文本
            txt = re.sub(r'<[^>]+>', ' ', inner)
            txt = re.sub(r'\s+', ' ', txt).strip()
            if txt and 1 <= len(txt) <= 40:
                a["texts"].append(txt)
            # 图(优先 data-src,fallback 到 src)
            for im in self._IMG_RE.finditer(inner):
                src = im.group(1) or im.group(2)
                if not src:
                    continue
                if src.startswith("data:image/gif"):  # 1x1 占位
                    continue
                a["pics"].append(src)
                break  # 第一个非占位图就够
            # data-slide-bg / data-poster(在 <a> 属性或 inner 里)
            pm = self._PIC_ATTR_RE.search(inner)
            if pm and pm.group(1):
                a["pics"].append(pm.group(1))
            # 整段 <a> 标签里的 data-slide-bg
            sm = re.search(r'data-slide-bg\s*=\s*"([^"]+)"', full_tag)
            if sm and sm.group(1):
                a["pics"].append(sm.group(1))
            # 备注
            rm = self._REMARK_RE.search(inner)
            if rm and rm.group(1).strip():
                a["remarks"].append(rm.group(1).strip())

        # 已知的"非视频" slug(子分类、辅助页)
        non_video_slugs = set(self._non_video_slugs)
        for c in CLASSES:
            non_video_slugs.update(self._sub_slugs.get(c['type_id'], set()))

        cards = []
        for path, a in agg.items():
            slug = a["slug"]
            cat = a["cat"]
            # 自动发现子分类:如果一个聚合结果无图 + 无标题 + slug 唯一(且短),
            # 很可能是子分类按钮(如 /movie/kongbupian)
            if not a["pics"] and not a["titles"] and not any(
                2 <= len(t) <= 20 and not re.match(r'^[a-z0-9\-_\s]+$', t)
                for t in a["texts"]
            ):
                # 像子分类(只有拼音 slug 没图没中文):加黑名单
                self._sub_slugs.setdefault(cat, set()).add(slug)
                continue
            # 复合 slug 启发式:slug 含 '-' 且前缀是已知子分类 → 也是子分类
            # 例: /movie/dongzuo-2018 (动作-2018) /movie/dongzuo-dalu (动作-大陆)
            if "-" in slug:
                prefix = slug.split("-", 1)[0]
                if prefix in self._sub_slugs.get(cat, set()):
                    self._sub_slugs.setdefault(cat, set()).add(slug)
                    continue
            if slug in non_video_slugs:
                continue
            # 标题优先级:title 属性 > 内部 title/name > 纯文本
            title = ""
            for t in a["titles"]:
                if t and not re.match(r'^[a-z0-9\-_\s]+$', t):  # 不是纯拼音
                    title = t
                    break
            if not title and a["titles"]:
                title = a["titles"][0]
            if not title:
                for t in a["texts"]:
                    if t and 2 <= len(t) <= 30 and not re.match(r'^[a-z0-9\-_\s]+$', t):
                        title = t
                        break
            if not title:
                continue
            # 图片:取第一个非 data: 的图
            pic = ""
            for p in a["pics"]:
                if p and not p.startswith("data:") and p != "/template/mizhiady/statics/images/loading.png":
                    pic = p
                    break
            pic = self._abs(pic) if pic else ""
            # 备注
            remark = a["remarks"][0] if a["remarks"] else "HD"
            cards.append({
                "vod_id": path,
                "vod_name": title.strip(),
                "vod_pic": pic,
                "vod_remarks": remark or "HD",
            })
            if len(cards) >= limit:
                break
        return cards

    # ===== 详情页 player 解析 =====
    # mizhiady 模板把每个播放源声明为全局 var player_xxxx = { JSON };
    # JSON 里有嵌套 {} / 字符串,不能用 .*? 非贪婪,改成手写平衡括号
    _PLAYER_START_RE = re.compile(r'(?:var\s+)?(player_[a-z]{3,8})\s*=\s*\{')
    # 详情页的 sid 子页:/movie/{id}/{episode}?sid=N
    _SID_LI_RE = re.compile(
        r'<li[^>]+class="[^"]*player_name[^"]*"[^>]*data-sid="(\d+)"[^>]*>.*?'
        r'data-from="([^"]+)"',
        re.S
    )

    def _extract_balanced_json(self, text, start):
        """从 start 位置开始,提取平衡的 {...} 块(支持字符串内的括号)"""
        if start >= len(text) or text[start] != '{':
            return None, start
        i = start
        depth = 0
        in_str = False
        esc = False
        while i < len(text):
            c = text[i]
            if esc:
                esc = False
            elif c == '\\' and in_str:
                esc = True
            elif c == '"':
                in_str = not in_str
            elif not in_str:
                if c == '{':
                    depth += 1
                elif c == '}':
                    depth -= 1
                    if depth == 0:
                        return text[start:i+1], i+1
            i += 1
        return None, start

    def _parse_players(self, html):
        """从单个详情页 HTML 解析出所有 player_xxxx(可能只有 sid=1 一个)"""
        if not html:
            return []
        players = []
        for m in self._PLAYER_START_RE.finditer(html):
            pname = m.group(1)
            raw, _ = self._extract_balanced_json(html, m.end() - 1)
            if not raw:
                continue
            try:
                data = json.loads(raw)
            except Exception:
                try:
                    data = json.loads(raw.replace('\\/', '/'))
                except Exception:
                    continue
            vid = data.get("id", "")
            sid = int(data.get("sid", 1))
            nid = data.get("nid", 1)
            from_name = (data.get("from") or "").strip()
            url = (data.get("url") or "").strip()
            if not url or not vid:
                continue
            players.append({
                "name": from_name or pname[-4:],
                "url": url,
                "id": vid,
                "sid": sid,
                "nid": nid,
                "pname": pname,
            })
        return players

    def _parse_route_tabs(self, html):
        """从详情页提取所有线路 tab [(sid, from, episode_slug), ...]
        episode_slug 用于构造子页 URL(若 sid>1 才需要)"""
        if not html:
            return []
        tabs = []
        for m in self._SID_LI_RE.finditer(html):
            sid = int(m.group(1))
            from_name = m.group(2).strip()
            tabs.append((sid, from_name))
        return tabs

    # ===== 自动发现子分类 =====
    # 首次进入 /movie /tv 等时,从 HTML 抓 filter-li 链接,扩充 SUBCATS。
    # mizhiady 模板把所有维度的筛选用同一个 filter-li 类展示:
    # 顶级分类页:展示"类型"维度(动作/喜剧/...)
    # 子分类页(已选了一个维度后):展示"地区"/"语言"等剩余维度
    # 我们不去区分维度,只把所有 filter-li 加进 SUBCATS(总上限 60 个,够用)
    _FILTER_LI_RE = re.compile(
        r'<a[^>]+class="[^"]*filter-li[^"]*"[^>]+href="[^"]*/([a-z]+)/([a-z0-9\-]+)"[^>]*>([^<]{1,15})</a>',
        re.S | re.I
    )

    def _discover_subcats(self, cat, html):
        """从分类页 HTML 自动发现子分类,扩充 SUBCATS 和 _sub_slugs / FILTERS

        注意:这里 mizhiady 的 filter-li 把维度混合展示,我们用"按 slug 形态推断":
          - slug 是 4 位数字(19xx/20xx)        → 年份
          - slug 含 - 且前缀是已知子分类         → 复合筛选(地区+类型)
          - slug 在已知地区白名单               → 地区
          - 其他                              → 类型

        只在确实发现新 slug 时才标 _subcat_loaded,否则允许外部继续触发抓 sub。
        """
        if not html:
            return
        # 如果 cat 已完全加载(枚举 + filter-li),跳过
        if cat in self._subcat_loaded:
            return
        new_found = 0
        for m in self._FILTER_LI_RE.finditer(html):
            c, slug, name = m.group(1), m.group(2), m.group(3).strip()
            if c != cat:
                continue
            if slug in ('all', '') or not name:
                continue
            # 已存在(同 slug)跳过
            if any(it['v'] == slug for it in SUBCATS.get(cat, [])):
                self._sub_slugs.setdefault(cat, set()).add(slug)
                continue
            # 同名但 slug 不同 → 用站点真实 slug 覆盖(纠正内置猜测,防 404)
            same_name = next((it for it in SUBCATS.get(cat, []) if it.get('n') == name), None)
            if same_name is not None:
                old = same_name.get('v')
                if old and old != slug:
                    self._sub_slugs.setdefault(cat, set()).discard(old)
                same_name['v'] = slug
                self._sub_slugs.setdefault(cat, set()).add(slug)
                new_found += 1
                continue
            # 上限:每个分类最多 60 个
            if sum(1 for it in SUBCATS.get(cat, []) if it.get('v')) >= 60:
                continue
            SUBCATS.setdefault(cat, []).append({"n": name, "v": slug})
            self._sub_slugs.setdefault(cat, set()).add(slug)
            new_found += 1

        # 同步 FILTERS(让 TVBox 客户端能看到新增的子分类)
        items = [{"n": "全部", "v": ""}]
        seen_v = {""}
        for it in SUBCATS.get(cat, []):
            if it.get('v') and it['v'] not in seen_v:
                items.append(it)
                seen_v.add(it['v'])
        FILTERS.setdefault(cat, [
            {"key": "class", "name": "类型", "value": items}
        ])
        FILTERS[cat][0]['value'] = items

        # 只在确实发现了新 slug 时才标 loaded(否则外部会再触发抓 sub)
        if new_found > 0:
            self._subcat_loaded.add(cat)

    def _warmup_subcats(self):
        """后台预热:进每个分类 + 一个常见子分类,扩充 _subcat_loaded。
        这让 homeContent() 返回时 FILTERS 已经有丰富子分类。
        """
        # 不重复 main 调用导致并发问题
        time.sleep(0.5)
        for c in CLASSES:
            cat = c["type_id"]
            try:
                # 抓顶级分类页
                html = self._http_get(HOST + "/" + cat, use_cache=True, ttl=180)
                if html:
                    self._discover_subcats(cat, html)
                # 再抓第一个有意义的子分类(暴露更多维度)
                first_sub = SUBCATS.get(cat, [{}])[1].get("v") if len(SUBCATS.get(cat, [])) > 1 else None
                if first_sub:
                    html = self._http_get(f"{HOST}/{cat}/{first_sub}", use_cache=True, ttl=180)
                    if html:
                        self._discover_subcats(cat, html)
            except Exception:
                pass

    def _sub_url_for(self, base_path, sid):
        """构造 sid 对应的子页 URL(优先匹配 li 里的 href)"""
        # 常见模式:/movie/xxx/play-1  /movie/xxx/hd?sid=2
        # 简化:用 ?sid=N 兜底(实际 mizhiady 需要真实 episode slug)
        # 真实 slug 在 li 内部 <a href="..."> 中,这里只兜底
        return f"{base_path}?sid={sid}"

    # ===== 详情页 元信息 =====
    def _parse_detail_meta(self, html):
        if not html:
            return {}
        meta = {}
        # 标题
        tm = re.search(r'<title>([^<]+?)[\s_]', html)
        if tm:
            meta["vod_name"] = tm.group(1).strip()
        # 海报(og:image 优先)
        og = re.search(r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']', html)
        if og:
            meta["vod_pic"] = og.group(1)
        # 简介
        cm = re.search(r'class="[^"]*(?:vod-content|detail-content|content-desc)[^"]*"[^>]*>([^<]{10,500})', html, re.S)
        if cm:
            meta["vod_content"] = re.sub(r'\s+', ' ', cm.group(1)).strip()
        # 主演、导演、类型
        for key, patterns in [
            ("vod_actor", [r'主\s*演[::]?\s*</span>\s*<span[^>]*>([^<]+)', r'主演[::]?\s*([^<\n]+)']),
            ("vod_director", [r'导\s*演[::]?\s*</span>\s*<span[^>]*>([^<]+)', r'导演[::]?\s*([^<\n]+)']),
            ("vod_year", [r'(20\d{2})年?']),
            ("vod_area", [r'(?:地区|地区[::]?)\s*</span>\s*<span[^>]*>([^<]+)', r'地区[::]?\s*([^<\n]{2,30})']),
        ]:
            for p in patterns:
                rm = re.search(p, html)
                if rm:
                    meta[key] = rm.group(1).strip()
                    break
        return meta

    # ============================================================
    # 首页
    # ============================================================

    def homeContent(self, filter):
        return {
            "class": CLASSES,
            "filters": FILTERS,
        }

    def homeVideoContent(self):
        """首页推荐:从首页 SSR 解析卡片(有缓存)"""
        now = time.time()
        if self._home_cache and now - self._home_cache_time < self._cache_ttl:
            return {"list": self._home_cache}

        html = self._http_get(HOST + "/", ttl=self._cache_ttl)
        cards = self._parse_cards(html, limit=72)
        # 过滤掉导航链接(分类页 slug 是 "movie"/"tv" 等已在 _parse_cards 滤掉)
        self._home_cache = [{
            "vod_id": c["vod_id"],
            "vod_name": c["vod_name"],
            "vod_pic": c["vod_pic"],
            "vod_remarks": c["vod_remarks"],
        } for c in cards]
        self._home_cache_time = now
        return {"list": self._home_cache}

    # ============================================================
    # 分类列表
    # ============================================================

    def categoryContent(self, tid, pg, filter, extend):
        try:
            page = max(int(pg or 1), 1)
            tid = str(tid or "").strip()
            if not tid:
                return {"page": 1, "pagecount": 1, "limit": 30, "total": 0, "list": []}

            # extend 里可能有 sub slug(class 字段)
            sub = ""
            if extend:
                if isinstance(extend, dict):
                    sub = (extend.get("class") or "").strip()
                elif isinstance(extend, str):
                    try:
                        ext = json.loads(extend)
                        sub = (ext.get("class") or "").strip()
                    except Exception:
                        pass

            # 拼路径: /movie/dongzuo?page=1
            if sub and sub != "all":
                path = f"/{tid}/{sub}"
            else:
                path = f"/{tid}"
            if page > 1:
                path += f"?page={page}"

            url = HOST + path
            html = self._http_get(url, ttl=self._cache_ttl)
            # 首次访问该分类时,自动发现子分类(类型/地区/年份)
            # 注意:子分类页面(传入 sub)也会暴露新的 filter-li 链接,
            # 比如 /movie/dongzuo 会展示"地区/语言"维度的链接
            if html and tid in {c["type_id"] for c in CLASSES}:
                try:
                    self._discover_subcats(tid, html)
                    # 进一步:如果该 cat 还没加载完,且这次没 sub,主动抓一个 sub 拿更多维度
                    if not sub and tid not in self._subcat_loaded:
                        # 找第一个 sub slug
                        first_sub = next(
                            (it['v'] for it in SUBCATS.get(tid, [])[1:] if it.get('v')),
                            None
                        )
                        if first_sub:
                            sub_html = self._http_get(
                                HOST + "/" + tid + "/" + first_sub,
                                use_cache=True, ttl=self._cache_ttl
                            )
                            if sub_html:
                                self._discover_subcats(tid, sub_html)
                except Exception:
                    pass
            cards = self._parse_cards(html, limit=60)

            # 二级分类空列表自愈:可能 slug 失效,补拉顶级分类页真实子分类,并用其内容兜底
            if not cards and sub and sub != "all" and tid in {c["type_id"] for c in CLASSES}:
                try:
                    cat_html = self._http_get(HOST + "/" + tid, ttl=self._cache_ttl)
                    if cat_html:
                        self._discover_subcats(tid, cat_html)
                        cards = self._parse_cards(cat_html, limit=60)
                except Exception:
                    pass

            return {
                "list": [{
                    "vod_id": c["vod_id"],
                    "vod_name": c["vod_name"],
                    "vod_pic": c["vod_pic"],
                    "vod_remarks": c["vod_remarks"],
                } for c in cards],
                "page": page,
                "pagecount": 999,        # mizhiady 没明确分页,伪装大数字让客户端可继续翻
                "limit": 30,
                "total": 999,
            }
        except Exception:
            return {"page": 1, "pagecount": 1, "limit": 30, "total": 0, "list": []}

    # ============================================================
    # 详情页
    # ============================================================
    # mizhiady 模板:每条线路是独立子页(/movie/{slug}/{episode}?sid=N)
    # 必须并发抓所有 sid 的子页才能拿到完整多线路

    _EPISODE_HREF_RE = re.compile(
        r'<a[^>]+href="([^"]+)"[^>]*data-(?:toggle|tab)[^>]*class="[^"]*swiper-slide-text[^"]*"',
        re.S
    )

    def detailContent(self, ids):
        try:
            if isinstance(ids, str):
                ids = [ids]
            if not ids:
                return {"list": []}
            raw_id = str(ids[0]).strip()
            if not raw_id:
                return {"list": []}
            # vod_id 可能是 /movie/xxx 或 http://...
            if raw_id.startswith("http"):
                from urllib.parse import urlparse
                path = urlparse(raw_id).path
            else:
                path = raw_id
            if not path.startswith("/"):
                path = "/" + path
            # 去掉尾部 / 和 ? 后参数(可能有 sid 残留)
            path = path.split("?")[0].rstrip("/")
            url = HOST + path

            # 1) 主详情页(sid=1)
            html = self._http_get(url, ttl=self._detail_ttl)
            if not html:
                return {"list": []}

            meta = self._parse_detail_meta(html)
            players = self._parse_players(html)

            # 2) 解析所有线路 tab
            sub_urls = {}  # sid -> sub_url
            for m in re.finditer(r'data-sid="(\d+)"', html):
                sid = int(m.group(1))
                seg = html[m.start():m.start()+3000]
                um = re.search(r'href="([^"]+?\?sid=' + str(sid) + r'(?:&[^"]*)?)"', seg)
                if um:
                    href = um.group(1)
                    if href.startswith("http"):
                        sub_urls[sid] = href
                    else:
                        sub_urls[sid] = self._abs(href)

            # 3) 并发抓其他 sid 的子页
            other_sids = [s for s in sub_urls if s != 1 and s > 1]
            if other_sids:
                from concurrent.futures import ThreadPoolExecutor, as_completed
                def fetch_one(sid):
                    return sid, self._http_get(
                        sub_urls[sid], ttl=self._detail_ttl,
                        use_cache=True, timeout=8
                    )
                with ThreadPoolExecutor(max_workers=min(6, len(other_sids))) as pool:
                    futures = [pool.submit(fetch_one, s) for s in other_sids]
                    for fut in as_completed(futures, timeout=12):
                        try:
                            sid, h = fut.result(timeout=8)
                            if h:
                                ps = self._parse_players(h)
                                for p in ps:
                                    p["sid"] = sid
                                players.extend(ps)
                        except Exception:
                            continue

            # 4) **兜底**:如果没拿到任何 player_xxxx(单线路 / 短剧 / JS 异步加载)
            #    但页面上有 data-from 线路信息,给壳子一组通用解析器嗅探。
            #    解析器收到我们的空 source,会自己搜索/抓页面里的视频源。
            if not players:
                froms = list(set(re.findall(r'data-from="([^"]+)"', html)))
                # 兜底解析器候选池(运行时随机/顺序给壳子试)
                parsers_pool = [
                    "https://svip.qlplayer.cyou/?url={url}",
                    "https://www.hnjiexi.com/m3u8/?url={url}",
                    "https://vip.zykbf.com/?url={url}",
                    "https://ffzyplayer.com/?url={url}",
                ]
                # 如果有 from,优先用专用解析器
                for fn in froms:
                    p = self._parser_map.get(fn)
                    if p and p not in parsers_pool:
                        parsers_pool.insert(0, p)
                # 给每个解析器做一个"线路"
                for i, p in enumerate(parsers_pool[:4]):
                    # url 用本详情页 path(很多解析器支持拿当前页 url 解析)
                    placeholder = urllib.parse.quote(url, safe="")
                    url_with_placeholder = p.replace("{url}", placeholder)
                    players.append({
                        "name": froms[0] if froms else f"线路{i+1}",
                        "url": url_with_placeholder,
                        "id": path.strip("/"), "sid": 1, "nid": 1,
                        "pname": f"player_fb{i}",
                    })

            if not players:
                return {"list": []}

            # 去重(sid, nid) 重复
            seen = set()
            unique = []
            for p in players:
                k = (p["sid"], p["nid"])
                if k in seen:
                    continue
                seen.add(k)
                unique.append(p)
            players = unique

            # 按线路优先级排序:直链 > 解析器 > 官源
            def priority(p):
                u = p["url"].lower()
                if ".m3u8" in u or ".mp4" in u:
                    return 0
                if "qlplayer" in u or "parse" in u or "jx" in u or "player/?url=" in u:
                    return 1
                return 2
            players.sort(key=priority)

            # 构造 TVBox 播放源
            from_counter = {}
            play_from = []
            play_url = []
            for p in players:
                name = p["name"] or p["pname"]
                from_counter[name] = from_counter.get(name, 0) + 1
                if from_counter[name] > 1:
                    name = f"{name}{from_counter[name]}"
                ep = f"第{p['nid']}集" if p.get("nid") and p["nid"] > 1 else "播放"
                play_from.append(name)
                play_url.append(f"{ep}${p['url']}")

            vod = {
                "vod_id": path,
                "vod_name": meta.get("vod_name", ""),
                "vod_pic": meta.get("vod_pic", ""),
                "type_name": "",
                "vod_year": meta.get("vod_year", ""),
                "vod_area": meta.get("vod_area", ""),
                "vod_remarks": "HD",
                "vod_actor": meta.get("vod_actor", "").lstrip("：: \t"),
                "vod_director": meta.get("vod_director", "").lstrip("：: \t"),
                "vod_content": meta.get("vod_content", ""),
                "vod_play_from": "$$$".join(play_from) if play_from else "饭搭子",
                "vod_play_url": "$$$".join(play_url) if play_url else "",
            }
            return {"list": [vod]}
        except Exception:
            return {"list": []}

    # ============================================================
    # 详情页
    # ============================================================
    # mizhiady 模板:每条线路(sid)下有多个剧集/版本,每个都对应一个独立子页
    #   /tv/{slug}/{ep}?sid={sid}   或  /movie/{slug}/{version}?sid={sid}
    # 子页里 player_aaaa.url 就是直链 m3u8。
    # 策略:detailContent 只做"目录"快速返回(真实线路名 + 各集子页URL),不抓子页;
    #      用户点击某集时由 playerContent 去抓那一个子页拿直链 → 详情秒开、不会拖慢。
    _SID_TAB_RE = re.compile(r'<li[^>]*data-sid="(\d+)"[^>]*>(.*?)</li>', re.S)
    _SID_NAME_RE = re.compile(
        r'data-name-for="\d+"[^>]*>([^<]+)<|mzady-route__name[^>]*>([^<]+)<|swiper-slide-text[^>]*>([^<]{1,8})<'
    )
    # 剧集/版本子页链接: 形如 /{cat}/{slug}/{sub}?sid=N 或 /{cat}/{slug}/{ep}(默认线路)
    _EP_LI_RE = re.compile(
        r'<a[^>]+href="([^"]*?/(?:movie|tv|dongman|zongyi|tiyu|duanju)/[a-z0-9\-]+/[A-Za-z0-9\-]+'
        r'(?:\?[^"]*)?)"[^>]*>(.*?)</a>',
        re.S | re.I
    )
    _NAV_SLUG_RE = re.compile(r'^[a-z0-9\-_]+$')

    def _parse_detail_lazy(self, html):
        """一次遍历详情主页面,返回 (sid->线路信息, 集列表)。
        sid_info: {sid: {'name':真实名,'from':解析器代号}}
        ep_list:  [(集名, 子页绝对URL, sid)]
        """
        sid_info = {}
        for m in self._SID_TAB_RE.finditer(html):
            sid = int(m.group(1)); inner = m.group(2)
            fm = re.search(r'data-from="([^"]+)"', inner)
            name = ""
            nm = self._SID_NAME_RE.search(inner)
            if nm:
                name = (nm.group(1) or nm.group(2) or nm.group(3) or "").strip()
            # data-name-for 里的就是真实线路展示名(可能是中文 也可能英文品牌如 bilibili),原样保留
            sid_info.setdefault(sid, {'name': name or (fm.group(1) if fm else ''), 'from': (fm.group(1) if fm else '')})
            if name:
                sid_info[sid]['name'] = name

        ep_list = []
        seen = set()
        for m in self._EP_LI_RE.finditer(html):
            href, inner = m.group(1), m.group(2)
            text = re.sub(r'<[^>]+>', ' ', inner)
            text = re.sub(r'\s+', ' ', text).strip()
            # 排除辅助页/反馈链接(href 里带 gbook/history/about 或 url= 转义的都是误匹配)
            if any(k in href for k in ('gbook', '/history', '/about', 'url=')):
                continue
            if not text or len(text) > 24:
                continue
            # 排除分类/筛选等非集链接
            if self._NAV_SLUG_RE.match(text) and '云' not in text and '集' not in text:
                continue
            # 排除明确的上/下集导航按钮(不是真实集名)
            if text in ('上集', '下集', '上一集', '下一集'):
                continue
            sm = re.search(r'sid=(\d+)', href)
            sid = int(sm.group(1)) if sm else 1   # 无 sid → 默认线路(sid=1)
            key = (sid, href)
            if key in seen:
                continue
            seen.add(key)
            ep_list.append((text, self._abs(href), sid))
        return sid_info, ep_list

    def _fetch_player_direct(self, page_url):
        """抓一个 fdzys 集/详情子页,取 player_aaaa.url(直链)。失败返回空串。"""
        try:
            html = self._http_get(self._abs(page_url), use_cache=True, ttl=self._detail_ttl, timeout=10)
            if not html:
                return ""
            i = html.find('player_aaaa=')
            if i < 0:
                i = html.find('player_')
            if i < 0:
                return ""
            j = html.find('{', i)
            if j < 0:
                return ""
            raw, _ = self._extract_balanced_json(html, j)
            if not raw:
                return ""
            data = json.loads(raw)
            return (data.get('url') or '').replace('\\/', '/')
        except Exception:
            return ""

    def detailContent(self, ids):
        try:
            if isinstance(ids, str):
                ids = [ids]
            if not ids:
                return {"list": []}
            raw_id = str(ids[0]).strip()
            if not raw_id:
                return {"list": []}
            if raw_id.startswith("http"):
                from urllib.parse import urlparse
                path = urlparse(raw_id).path
            else:
                path = raw_id
            if not path.startswith("/"):
                path = "/" + path
            path = path.split("?")[0].rstrip("/")
            url = HOST + path

            html = self._http_get(url, ttl=self._detail_ttl)
            if not html:
                return {"list": []}

            meta = self._parse_detail_meta(html)
            sid_info, ep_list = self._parse_detail_lazy(html)

            # 按 sid 归集各线路的剧集: name -> url
            lines = {}    # sid -> [(集名, url), ...]  保持顺序
            for name, epurl, sid in ep_list:
                lines.setdefault(sid, []).append((name, epurl))

            # 兜底:某线路没收集到子页集(如电影默认线路),用主页面 player_aaaa 直链补一条
            main_direct = ""
            if not all(lines.get(s) for s in sid_info):
                main_direct = self._fetch_player_direct(url)
            for sid in sid_info:
                if not lines.get(sid) and main_direct:
                    lines.setdefault(sid, []).append(("正片", main_direct))

            # 无线路信息但有集 → 按 sid 造默认名
            for sid in list(lines):
                if sid not in sid_info:
                    sid_info[sid] = {'name': '', 'from': ''}

            play_from = []
            play_url_seg = []
            used_names = {}
            # 保证稳定顺序:按 sid 排序
            for sid in sorted(lines, key=int):
                info = sid_info.get(sid, {})
                raw_nm = (info.get('name') or '').strip()
                if raw_nm:
                    nm = raw_nm                     # 真实展示名(中文/英文品牌)原样保留
                else:
                    nm = (info.get('from') or '').strip()
                    if re.match(r'^[a-z0-9\-]+$', nm):
                        nm = '线路%d' % sid        # 兜底: 解析器代号 → 线路N
                used_names[nm] = used_names.get(nm, 0) + 1
                if used_names[nm] > 1:
                    nm = '%s%d' % (nm, used_names[nm])
                play_from.append(nm)
                eps_str = '#'.join('%s$%s' % (n, u) for n, u in lines[sid])
                play_url_seg.append(eps_str)

            vod = {
                "vod_id": path,
                "vod_name": meta.get("vod_name", ""),
                "vod_pic": meta.get("vod_pic", ""),
                "type_name": "",
                "vod_year": meta.get("vod_year", ""),
                "vod_area": meta.get("vod_area", ""),
                "vod_remarks": "HD",
                "vod_actor": meta.get("vod_actor", "").lstrip("：: \t"),
                "vod_director": meta.get("vod_director", "").lstrip("：: \t"),
                "vod_content": meta.get("vod_content", ""),
                "vod_play_from": "$$$".join(play_from) if play_from else "饭搭子",
                "vod_play_url": "$$$".join(play_url_seg) if play_url_seg else "",
            }
            return {"list": [vod]}
        except Exception:
            return {"list": []}


    # ============================================================
    # 搜索
    # ============================================================
    # mizhiady 模板搜索是异步加载,/index.php/vod/search 路由 404
    # 但 suggest 接口直接返回搜索结果(每条含 name/en/pic/id)
    # en 是拼音 slug,详情页就是 /movie/{en}

    _SUGGEST_URL = HOST + "/index.php/ajax/suggest?mid=1&wd={wd}&limit=20"

    def searchContent(self, key, quick, pg="1"):
        try:
            kw = (key or "").strip()
            if not kw:
                return {"list": []}
            url = self._SUGGEST_URL.format(wd=urllib.parse.quote(kw))
            raw = self._http_get(url, use_cache=True, ttl=30)
            if not raw:
                return {"list": []}
            data = json.loads(raw)
            if data.get("code") != 1:
                return {"list": []}
            results = []
            for item in data.get("list", []):
                en = (item.get("en") or "").strip()
                name = (item.get("name") or "").strip()
                pic = item.get("pic") or ""
                if not en or not name:
                    continue
                # en 已经是 slug,详情页就是 /<cat>/<en>;猜分类(简化:默认 movie,也可探测)
                # 实际上 suggest 没返回分类,稳妥做法是默认 movie,然后播放器/详情自动适配
                vod_id = f"/movie/{en}"
                results.append({
                    "vod_id": vod_id,
                    "vod_name": name,
                    "vod_pic": self._abs(pic) if pic and not pic.startswith("http") else pic,
                    "vod_remarks": "HD",
                })
            return {"list": results}
        except Exception:
            return {"list": []}

    # ============================================================
    # 播放解析
    # ============================================================

    # 判断是否为直链媒体
    _DIRECT_EXTS = (".m3u8", ".mp4", ".flv", ".mkv", ".ts", ".mov")
    # 判断是否为官源
    _OFFICIAL_KEYS = (
        "v.qq.com", "qq.com", "iqiyi.com", "qiyi.com", "youku.com",
        "mgtv.com", "bilibili.com", "le.com", "sohu.com", "pptv.com",
    )

    def _is_direct(self, url):
        u = (url or "").lower()
        return any(e in u for e in self._DIRECT_EXTS)

    def _is_official(self, url):
        u = (url or "").lower()
        return any(k in u for k in self._OFFICIAL_KEYS) and not self._is_direct(u)

    def _is_parser(self, url):
        u = (url or "").lower()
        return any(k in u for k in ("qlplayer", "parse", "jx", "player/?url="))

    def _referer_for(self, url):
        try:
            if "://" in url:
                scheme = url.split("://")[0]
                host = url.split("://")[1].split("/")[0]
                return f"{scheme}://{host}/"
        except Exception:
            pass
        return HOST + "/"

    def _looks_like_site_page(self, url):
        u = (url or '').lower()
        if self._is_direct(u) or self._is_parser(u) or self._is_official(u):
            return False
        return (HOST.rstrip('/') in u) or u.startswith('/')

    def playerContent(self, flag, id, vipFlags):
        if not id:
            return {"parse": 0, "playUrl": "", "url": ""}
        play_url = str(id).replace("\\/", "/").strip()
        if not play_url:
            return {"parse": 0, "playUrl": "", "url": ""}

        # 0. fdzys 集/详情子页 → 抓该页拿真实直链(懒加载核心)
        if self._looks_like_site_page(play_url):
            direct = self._fetch_player_direct(play_url)
            if direct:
                play_url = direct
                # 继续走下面的直链判断,给出正确 header

        common_header = {
            "User-Agent": UA,
            "Referer": self._referer_for(play_url),
        }

        # 1. 直链 m3u8 / mp4 → 直接给播放器
        if self._is_direct(play_url):
            is_m3u8 = ".m3u8" in play_url.lower()
            return {
                "parse": 0,
                "playUrl": "",
                "url": play_url,
                "header": common_header,
                "format": "application/x-mpegURL" if is_m3u8 else "",
                "contentType": "application/x-mpegURL" if is_m3u8 else "",
            }

        # 2. 解析器 URL(已拼好 source)— parse=0 让壳子当 iframe 加载
        if self._is_parser(play_url) and "url=" in play_url.lower():
            return {
                "parse": 0,
                "playUrl": "",
                "url": play_url,
                "header": {
                    "User-Agent": UA,
                    "Referer": self._referer_for(play_url),
                },
            }

        # 3. 解析器前缀(没 source)— parse=1 让壳子嗅探
        if self._is_parser(play_url):
            return {
                "parse": 1,
                "playUrl": "",
                "url": play_url,
                "header": {
                    "User-Agent": UA,
                    "Referer": self._referer_for(play_url),
                },
            }

        # 4. 官源 → 走外层兜底解析器
        if self._is_official(play_url):
            return {
                "parse": 1,
                "playUrl": "",
                "url": FALLBACK_PARSER.replace("{url}", urllib.parse.quote(play_url, safe="")),
                "header": {
                    "User-Agent": UA,
                    "Referer": HOST + "/",
                },
            }

        # 5. 其他 → 试探嗅探
        return {
            "parse": 1,
            "playUrl": "",
            "url": play_url,
            "header": common_header,
        }


    # ===== 本地代理 =====
    def localProxy(self, param):
        return [200, "video/MP2T", b"", ""]

    # ===== 清理 =====
    def destroy(self):
        self._page_cache.clear()
        self._home_cache.clear()
        self._home_cache_time = 0

    def close(self):
        self.destroy()
