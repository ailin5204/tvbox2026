# -*- coding: utf-8 -*-
# 大马猴影视 - 检修版（T4 契约 / Jython 2.7 兼容）
# 分类接口: /api.php/web/filter/vod?type_id=23/22/24/25&page=1&sort=hits
# 详情接口: /api.php/web/vod/get_detail?vod_id=xxx
# 聚合线路: /api.php/web/internal/search_aggregate?vod_id=xxx  优先提取 m3u8 直链
# 注意：filter 接口会无视 type_id 混回各类，分类页须本地按真实 type_id 二次过滤。
# 正常卡图（用户未说大图，不加 style 字段）。

import sys
import json
import re

_PY2 = sys.version_info[0] == 2
if _PY2:
    _STR = basestring
else:
    _STR = str


def _txt(s):
    if s is None:
        return u''
    if isinstance(s, bytes):
        try:
            return s.decode('utf-8')
        except Exception:
            return s.decode('utf-8', 'ignore')
    if _PY2 and isinstance(s, str):
        try:
            return s.decode('utf-8')
        except Exception:
            return unicode(s, 'utf-8', 'ignore')
    if isinstance(s, _STR):
        return s
    try:
        return _txt(str(s))
    except Exception:
        return u''


def _quote_txt(s):
    # py2 下 urllib.quote 不接受 unicode，须先转 utf-8 字节。
    t = _txt(s)
    if _PY2:
        return quote(t.encode('utf-8'))
    return quote(t)


def _urlencode_params(params):
    # py2 下 urlencode 遇中文 unicode 会 KeyError，先转 utf-8 字节。
    if not _PY2:
        return urlencode(params, doseq=True)
    out = {}
    for k, v in (params or {}).items():
        kk = _txt(k).encode('utf-8')
        if isinstance(v, (list, tuple)):
            out[kk] = [_txt(x).encode('utf-8') for x in v]
        else:
            out[kk] = _txt(v).encode('utf-8')
    return urlencode(out, doseq=True)


try:
    from urllib.parse import urlencode, quote, unquote
except ImportError:
    from urllib import urlencode, quote, unquote

try:
    from html.parser import HTMLParser
except ImportError:
    from HTMLParser import HTMLParser


class _Resp(object):
    def __init__(self, text, content):
        self.text = text
        self.content = content
        self.status_code = 200


class _FallbackSpider(object):
    # BaseSpider 四级兜底之最后一档：壳子 base.spider 不可用时用 urllib 直取。
    def fetch(self, url, headers=None, timeout=12):
        try:
            import urllib2
        except ImportError:
            import urllib.request as urllib2
        req = urllib2.Request(_txt(url).encode('utf-8') if _PY2 else url)
        for k, v in (headers or {}).items():
            req.add_header(k, v)
        try:
            r = urllib2.urlopen(req, timeout=timeout)
            raw = r.read()
        except Exception:
            return _Resp(u'', b'')
        try:
            text = raw.decode('utf-8', 'ignore')
        except Exception:
            text = u''
        return _Resp(text, raw)

    def post(self, url, data=None, headers=None, timeout=12):
        return self.fetch(url, headers=headers, timeout=timeout)

    def getCache(self, key):
        return ''

    def setCache(self, key, value):
        return None

    def getProxyUrl(self):
        return ''


try:
    from base.spider import Spider as _BaseSpider
except Exception:
    _BaseSpider = _FallbackSpider


class _HTMLTextExtractor(HTMLParser):
    def __init__(self):
        # py2 里 HTMLParser 是旧式类，没有 super().__init__()，必须显式调基类。
        HTMLParser.__init__(self)
        self._text = []

    def handle_data(self, data):
        self._text.append(data)

    def get_text(self):
        return ''.join(self._text)


class Spider(_BaseSpider):
    def __init__(self):
        self.host = 'https://dmhyy.com'
        # 大马猴真实分类 ID 来自网页 /type/xx 和 XHR 返回：
        # /type/23 电影，/type/22 剧集，/type/24 动漫，/type/25 综艺
        self.classes = [
            {'type_id': '23', 'type_name': u'电影'},
            {'type_id': '22', 'type_name': u'剧集'},
            {'type_id': '24', 'type_name': u'动漫'},
            {'type_id': '25', 'type_name': u'综艺'},
        ]
        self.web_sign = ''

    def init(self, extend=''):
        try:
            if extend:
                if isinstance(extend, dict):
                    ext = extend
                else:
                    text = _txt(extend).strip()
                    ext = json.loads(text) if text.startswith('{') else {'site': text}
                site = ext.get('site') or ext.get('host') or ''
                if site:
                    self.host = _txt(site).split(',')[0].strip().rstrip('/')
                self.web_sign = ext.get('web-sign') or ext.get('web_sign') or self.web_sign
        except Exception:
            pass
        return None

    def _ensure_ready(self):
        if not getattr(self, 'host', ''):
            self.host = 'https://dmhyy.com'
        self.host = self.host.rstrip('/')

    def getName(self):
        return u'大马猴影视'

    def destroy(self):
        pass

    def isVideoFormat(self, url):
        # 选集字符串中经常是 .m3u8#下一集，不能只判断 ? 或结尾。
        return bool(re.search(r'\.(m3u8|mp4|flv|mkv|avi)(\?|#|$|\s)', _txt(url), re.I))

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        # 本脚本无代理需求；归一返回 3 元组 bytes，不返回 None。
        return [404, 'text/plain', b'']

    def _headers(self, referer=''):
        self._ensure_ready()
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/149.0.0.0 Safari/537.36',
            'Accept': 'application/json, text/plain, */*',
            'Accept-Language': 'zh-CN,zh;q=0.9',
            'Referer': referer or (self.host + '/'),
            'x-platform': 'web',
            'x-requested-with': 'XMLHttpRequest',
        }
        # 云朵站需要 web-sign；大马猴当前播放页 XHR 不需要。若 ext 显式提供则带上。
        if getattr(self, 'web_sign', ''):
            headers['web-sign'] = self.web_sign
        return headers

    def _api_get(self, path, params=None, referer=''):
        self._ensure_ready()
        params = params or {}
        qs = _urlencode_params(params)
        url = self.host + path + (('?' + qs) if qs else '')
        try:
            r = self.fetch(url, headers=self._headers(referer), timeout=12)
            text = getattr(r, 'text', '') or getattr(r, 'content', b'')
            text = _txt(text)
            if not text:
                return {}
            return json.loads(text)
        except Exception:
            return {}

    _NAMED_ENT = {
        'amp': '&', 'lt': '<', 'gt': '>', 'quot': '"', 'apos': "'",
        'nbsp': ' ', 'ldquo': u'\u201c', 'rdquo': u'\u201d',
        'lsquo': u'\u2018', 'rsquo': u'\u2019', 'hellip': u'\u2026',
        'mdash': u'\u2014', 'middot': u'\u00b7',
    }

    def _unescape_once(self, s):
        # 单遍正则替换：&amp;lt; 只解一层成 &lt;，绝不二次解成尖括号。
        def _rep(m):
            ent = m.group(1)
            try:
                if ent[:2] in ('#x', '#X'):
                    return unichr(int(ent[2:], 16)) if _PY2 else chr(int(ent[2:], 16))
                if ent[:1] == '#':
                    return unichr(int(ent[1:], 10)) if _PY2 else chr(int(ent[1:], 10))
            except Exception:
                return m.group(0)
            return self._NAMED_ENT.get(ent, m.group(0))
        return re.sub(r'&(#x?[0-9a-fA-F]+|\w+);', _rep, s)

    def _clean_text(self, s):
        # 先 strip 标签，再单次 unescape，禁止双重解码。
        s = _txt(s)
        s = re.sub(r'<[^>]+>', ' ', s)
        s = self._unescape_once(s)
        return re.sub(r'\s+', ' ', s).strip()

    def _html2text(self, html):
        try:
            p = _HTMLTextExtractor()
            p.feed(_txt(html))
            # 解析器已解过一次实体，这里只压空白，不再 unescape，避免二次解码。
            return re.sub(r'\s+', ' ', p.get_text()).strip()
        except Exception:
            return self._clean_text(html)

    def _tag_list(self, names):
        # 演员/类型写成可点击小标签；站内无字段时返回空串，不编造。
        out = []
        for n in names:
            n = self._clean_text(n)
            if n:
                out.append('[a=cr:{"name":"%s"}/]%s[/a]' % (n, n))
        return ','.join(out)

    def _split_names(self, v):
        if isinstance(v, list):
            parts = []
            for x in v:
                parts.extend(_txt(x).replace(u'\uFF0C', ',').split(','))
            return [p.strip() for p in parts if p.strip()]
        return [p.strip() for p in _txt(v).replace(u'\uFF0C', ',').split(',') if p.strip()]

    def _as_list(self, data):
        if isinstance(data, list):
            return data
        if isinstance(data, dict):
            for k in ('data', 'list', 'items', 'records', 'rows', 'vod_list'):
                v = data.get(k)
                if isinstance(v, list):
                    return v
                if isinstance(v, dict):
                    vv = self._as_list(v)
                    if vv:
                        return vv
        return []

    def _vod_item(self, item):
        if not isinstance(item, dict):
            return None
        vid = item.get('vod_id') or item.get('id') or item.get('vodId')
        name = item.get('vod_name') or item.get('name') or item.get('title')
        if not vid or not name:
            return None
        area = item.get('vod_area', '')
        cls = item.get('vod_class', '')
        if isinstance(area, list):
            area = ','.join([_txt(x) for x in area if x])
        if isinstance(cls, list):
            cls = ','.join([_txt(x) for x in cls if x])
        return {
            'vod_id': _txt(vid),
            'vod_name': self._clean_text(name),
            'vod_pic': _txt(item.get('vod_pic') or item.get('pic') or item.get('cover') or ''),
            'vod_remarks': _txt(item.get('vod_remarks') or item.get('remarks') or item.get('vod_douban_score') or item.get('vod_year') or ''),
            'vod_year': _txt(item.get('vod_year') or ''),
            'type_name': self._clean_text(item.get('type_name') or cls or ''),
            'vod_area': self._clean_text(area),
        }

    def _vod_list(self, data):
        arr = self._as_list(data)
        out = []
        seen = set()
        for item in arr:
            v = self._vod_item(item)
            if not v:
                continue
            if v['vod_id'] in seen:
                continue
            seen.add(v['vod_id'])
            out.append(v)
        return out


    def _category_match(self, item, real_tid):
        """大马猴的接口即使传 type_id=22，也会混入电影/动漫/综艺。
        所以必须在脚本内按真实 type_id/type_name 再过滤一次，避免所有分类显示相同内容。
        """
        if not isinstance(item, dict):
            return False
        real_tid = _txt(real_tid)
        item_tid = _txt(item.get('type_id') or item.get('typeId') or item.get('tid') or '')
        if item_tid == real_tid:
            return True
        name = _txt(item.get('type_name') or '')
        class_value = item.get('vod_class') or []
        if isinstance(class_value, list):
            cls = ','.join([_txt(x) for x in class_value if x])
        else:
            cls = _txt(class_value or '')
        text = name + ',' + cls
        if real_tid == '23':
            return (u'电影' in text or u'动作片' in text or u'剧情片' in text or u'喜剧片' in text) and u'电视剧' not in text
        if real_tid == '22':
            return any(k in text for k in (u'剧集', u'电视剧', u'国产剧', u'连续剧', u'韩剧', u'陆剧', u'欧美剧', u'日剧'))
        if real_tid == '24':
            return u'动漫' in text or u'动画' in text or u'国产动漫' in text or u'日韩动漫' in text
        if real_tid == '25':
            return u'综艺' in text or u'真人秀' in text
        return True

    def _filter_items_by_category(self, data, real_tid):
        arr = self._as_list(data)
        return [x for x in arr if self._category_match(x, real_tid)]

    def _home_list(self):
        # 首页推荐：电影热门（filter 接口混回各类，原样作热门推荐，不做分类过滤）。
        j = self._api_get('/api.php/web/filter/vod', {
            'type_id': '23',
            'page': '1',
            'sort': 'hits'
        }, self.host + '/type/23')
        return self._vod_list(j)

    def homeContent(self, filter):
        # 壳子首页渲染要求 list，只返 class 会显示“加载不出来”。
        return {'class': self.classes, 'filters': {}, 'list': self._home_list()}

    def homeVideoContent(self):
        return {'list': self._home_list()}

    def categoryContent(self, tid, pg, filter, extend):
        self._ensure_ready()
        page = _txt(pg or '1')
        sort = 'hits'
        if isinstance(extend, dict):
            sort = extend.get('sort') or extend.get('by') or sort

        # 真实 XHR 分类接口。注意大马猴不是 1/2/3/4，而是 23/22/24/25。
        # 这里保留一个兼容映射，防止旧配置或壳缓存还传入 1/2/3/4。
        tid_map = {'1': '23', '2': '22', '3': '24', '4': '25'}
        real_tid = tid_map.get(_txt(tid), _txt(tid))
        # 大马猴接口会混入其它分类，必须本地二次过滤。
        j = self._api_get('/api.php/web/filter/vod', {
            'type_id': real_tid,
            'page': page,
            'sort': sort
        }, self.host + '/type/' + real_tid)

        filtered_items = self._filter_items_by_category(j, real_tid)

        # 原稿“过滤后不足 8 条就补抓后 2 页”的逻辑已删：实测它会让第 N 页混入
        # N+1、N+2 页的条目，第 1 页与第 2 页重合 12 条、翻页全是重复标题。
        # 分类页只返回本页过滤结果（综艺这类小类本页 3 条也照常出，不空白即可）。
        try:
            cur_page = int(page)
        except Exception:
            cur_page = 1

        videos = self._vod_list(filtered_items)
        pagecount = 1
        total = len(videos)
        limit = 24
        if isinstance(j, dict):
            try:
                pagecount = int(j.get('pageCount') or j.get('pagecount') or (cur_page + 1 if videos else cur_page))
            except Exception:
                pagecount = cur_page + 1 if videos else cur_page
            try:
                total = int(j.get('total') or total)
            except Exception:
                total = len(videos)
            try:
                limit = int(j.get('limit') or limit)
            except Exception:
                limit = 24

        return {
            'list': videos,
            'page': cur_page,
            'pagecount': pagecount,
            'limit': limit,
            'total': total
        }

    def searchContent(self, key, quick, pg='1'):
        self._ensure_ready()
        wd = _txt(key or '').strip()
        page = _txt(pg or '1')
        if not wd:
            return {'list': [], 'page': int(page)}

        # 真实网页搜索接口（其余候选接口均 404/无效）
        paths = [
            ('/api.php/web/search/index', {'wd': wd, 'page': page}),
        ]
        for path, params in paths:
            j = self._api_get(path, params, self.host + '/search?keyword=' + _quote_txt(wd))
            videos = self._vod_list(j)
            if videos:
                out = {'list': videos, 'page': int(page)}
                if isinstance(j, dict):
                    try:
                        out['pagecount'] = int(j.get('pageCount') or j.get('pagecount') or int(page))
                    except Exception:
                        out['pagecount'] = int(page)
                    try:
                        out['total'] = int(j.get('total') or len(videos))
                    except Exception:
                        out['total'] = len(videos)
                return out
        return {'list': [], 'page': int(page)}

    def _first_detail(self, ids):
        vid = _txt(ids[0] if isinstance(ids, list) else ids)
        j = self._api_get('/api.php/web/vod/get_detail', {'vod_id': vid}, self.host + '/play/' + vid)
        arr = self._as_list(j)
        return (arr[0] if arr else {}), j

    def _aggregate_sources(self, vid):
        # 真实播放页会请求这个聚合接口，里面有很多站外直链 m3u8。必须使用 /play/vid referer 和 x-client。
        paths = [
            '/api.php/web/internal/search_aggregate',
            '/api.php/web/search_aggregate',
        ]
        for path in paths:
            j = self._api_get(path, {'vod_id': _txt(vid)}, self.host + '/play/' + _txt(vid))
            arr = self._as_list(j)
            if arr:
                return arr
        return []

    def _line_rank(self, src):
        name = _txt(src.get('site_name') or src.get('external_display_name') or src.get('vod_play_from') or '').lower()
        from_code = _txt(src.get('vod_play_from') or src.get('external_play_from') or '').lower()
        url = _txt(src.get('vod_play_url') or '')
        # 只要线路里已经是 m3u8/mp4，就按直链线路优先；decode_status 不再作为过滤条件。
        if re.search(r'\.(m3u8|mp4|flv)(\?|#|$|\s)', url, re.I):
            if u'暴风' in name or 'bfzy' in from_code:
                return 1
            if u'爱坤' in name or 'ikm3u8' in from_code:
                return 2
            if u'极速' in name or 'jsm3u8' in from_code:
                return 3
            if u'如意' in name or 'rym3u8' in from_code:
                return 4
            if u'量子' in name or 'lzm3u8' in from_code:
                return 5
            return 10
        if int(src.get('decode_status') or 0) == 0:
            return 50
        return 99

    def _build_sources(self, vid, detail):
        sources = []
        seen = set()

        def add_source(name, play_url):
            name = self._clean_text(name or '')
            play_url = _txt(play_url or '').strip()
            if not name or not play_url:
                return
            key = name + '|' + play_url[:80]
            if key in seen:
                return
            seen.add(key)
            sources.append((name, play_url))

        # 1. 优先用真实聚合接口，它返回的是可直接播放的 m3u8 线路。
        #    这类线路比 get_detail 里的 JD/腾讯编码线路更适合 TVBox。
        agg = self._aggregate_sources(vid)
        if agg:
            agg = sorted(agg, key=self._line_rank)
            for src in agg:
                play_url = _txt(src.get('vod_play_url') or '').strip()
                if not play_url:
                    continue
                # 只优先加入直链线路，避免详情页无播放器或线路过多卡死。
                if not re.search(r'\.(m3u8|mp4|flv)(\?|#|$|\s)', play_url, re.I):
                    continue
                line_name = (
                    src.get('site_name')
                    or src.get('external_display_name')
                    or src.get('external_play_from')
                    or src.get('vod_play_from')
                    or u'线路'
                )
                add_source(line_name, play_url)
                if len(sources) >= 4:
                    break

        # 2. 兜底：从 get_detail 里只提取含 m3u8/mp4 的线路，过滤 JD/QQ 这类需二次解析的超长线路。
        pf = _txt(detail.get('vod_play_from') or '')
        pu = _txt(detail.get('vod_play_url') or '')
        if pf and pu and len(sources) < 2:
            froms = pf.split('$$$')
            urls = pu.split('$$$')
            for idx, f in enumerate(froms):
                u = urls[idx] if idx < len(urls) else ''
                if not f or not u:
                    continue
                if not re.search(r'\.(m3u8|mp4|flv)(\?|#|$|\s)', u, re.I):
                    continue
                add_source(f, u)
                if len(sources) >= 4:
                    break

        # 3. 最后兜底：如果完全没有直链，再少量加入解析线路。
        if not sources and pf and pu:
            froms = pf.split('$$$')
            urls = pu.split('$$$')
            for idx, f in enumerate(froms[:3]):
                u = urls[idx] if idx < len(urls) else ''
                add_source(f, u)

        return sources

    def detailContent(self, ids):
        self._ensure_ready()
        if not ids:
            return {'list': []}
        vid = _txt(ids[0])
        detail, raw = self._first_detail([vid])

        if not detail:
            agg = self._aggregate_sources(vid)
            if agg:
                detail = agg[0]
            else:
                return {'list': []}

        area = detail.get('vod_area', '')
        cls = detail.get('vod_class', '')
        if isinstance(area, list):
            area = ','.join([_txt(x) for x in area if x])
        if isinstance(cls, list):
            cls = ','.join([_txt(x) for x in cls if x])

        sources = self._build_sources(vid, detail)
        # vod_play_url 整串约 2048B 截断：40 集单线约 6.3KB，必须按 ≤1900B 分段。
        from_lines, url_lines = [], []
        for line_name, play_url in sources:
            eps = [e for e in play_url.split('#') if e]
            if not eps:
                continue
            chunk, chunk_len, idx = [], 0, 1
            for ep in eps:
                blen = len(ep.encode('utf-8')) + 1
                if chunk and chunk_len + blen > 1900:
                    from_lines.append(line_name if idx == 1 else line_name + str(idx))
                    url_lines.append('#'.join(chunk))
                    idx += 1
                    chunk, chunk_len = [], 0
                chunk.append(ep)
                chunk_len += blen
            if chunk:
                from_lines.append(line_name if idx == 1 else line_name + str(idx))
                url_lines.append('#'.join(chunk))
        vod = {
            'vod_id': vid,
            'vod_name': self._clean_text(detail.get('vod_name') or ''),
            'vod_pic': _txt(detail.get('vod_pic') or ''),
            'vod_remarks': _txt(detail.get('vod_remarks') or ''),
            'type_name': self._tag_list(self._split_names(cls) if cls else [detail.get('type_name') or '']),
            'vod_year': _txt(detail.get('vod_year') or ''),
            'vod_area': self._clean_text(area),
            'vod_actor': self._tag_list(self._split_names(detail.get('vod_actor') or '')),
            'vod_director': self._tag_list(self._split_names(detail.get('vod_director') or '')),
            'vod_content': self._html2text(detail.get('vod_content') or ''),
            'vod_play_from': u'$$$'.join(from_lines),
            'vod_play_url': u'$$$'.join(url_lines),
        }
        return {'list': [vod]}

    def playerContent(self, flag, id, vipFlags):
        self._ensure_ready()
        url = _txt(id or '').strip()
        if not url:
            return {'parse': 0, 'url': ''}

        # 直链直接播放
        if url.startswith('http') and self.isVideoFormat(url):
            return {
                'parse': 0,
                'jx': 0,
                'url': url,
                'header': {
                    'User-Agent': 'Mozilla/5.0',
                    'Referer': self.host + '/'
                }
            }

        # 官方站外编码线路尝试用 decode 接口解析
        decode_candidates = [
            ('/api.php/web/decode/url', {'url': url}),
            ('/api.php/web/decode/url', {'play_url': url}),
            ('/api.php/web/decode/url', {'vod_url': url}),
        ]
        for path, params in decode_candidates:
            j = self._api_get(path, params, self.host + '/play')
            data = j.get('data') if isinstance(j, dict) else None
            final_url = ''
            headers = {}
            if isinstance(data, str):
                final_url = data
            elif isinstance(data, dict):
                final_url = data.get('url') or data.get('play_url') or data.get('playUrl') or data.get('video') or ''
                headers = data.get('header') or data.get('headers') or {}
            elif isinstance(j, dict):
                final_url = j.get('url') or j.get('play_url') or ''
                headers = j.get('header') or j.get('headers') or {}

            if final_url:
                return {
                    'parse': 0 if self.isVideoFormat(final_url) else 1,
                    'jx': 0 if self.isVideoFormat(final_url) else 1,
                    'url': final_url,
                    'header': headers or {'User-Agent': 'Mozilla/5.0', 'Referer': self.host + '/'}
                }

        # 腾讯/优酷/爱奇艺等网页地址交给壳解析
        if re.search(r'(v\.qq\.com|youku\.com|iqiyi\.com|mgtv\.com|bilibili\.com)', url, re.I):
            return {'parse': 1, 'jx': 1, 'url': url}

        # 其它未知地址也交给壳解析
        return {'parse': 1, 'jx': 1, 'url': url}
