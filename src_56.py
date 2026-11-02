# coding=utf-8
"""
目标站: 迷你影视 (lvmin.org)
模板: MacCMS 面包影视 (mianbaowang)
站点类型: 综合影视
支持: 首页, 分类(含二级筛选: 类型/年份/语言/字母), 搜索, 详情(多线路), 播放

本版修复(依据站点真实 HTML 核对):
1. 详情页线路/剧集解析重写: 面包模板的 h3 与 <ul class="stui-content__playlist"> 之间夹着
   div, 旧正则要求两者紧邻, 故所有线路都取不到; 现按 /play/{vid}_{sid}_{nid}.html 的
   线路号分组, 线路名取该组上方最近的 h3 标题, 支持多线路与分集。
2. 简介正则补 re.DOTALL 并优先使用 #desc 段落, 跨行简介不再为空。
3. 分类筛选路径改为分段拼接, tid/年份/语言/字母可同时生效。
4. 封面与相对地址统一拼成绝对地址。
5. 年份列表按当前年份动态生成。
6. 分页总数直接读页面 <span class="num">1/N</span>, 搜索多页走站点自身的 /search/page/N/wd/X.html。
7. 播放页 JSON 用正则加括号配对双保险提取, 补 base64 解密后的 percent 还原与非直链嗅探。
"""

import sys
import re
import json
import base64
import datetime
import urllib.parse

sys.path.append('..')
from base.spider import Spider


class Spider(Spider):
    # ===================== 初始化 =====================
    def init(self, extend=""):
        self.site_url = "https://www.lvmin.org"
        self.headers = {
            'User-Agent': 'Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'zh-CN,zh;q=0.9',
        }
        self.default_pic = 'https://pic.rmb.bdstatic.com/bjh/user/default.png'

        # ---- 一级分类 ----
        self.categories = {
            '1': '电影',
            '2': '电视剧',
            '5': '动漫',
            '29': '短剧',
            '37': '综艺',
        }

        # ---- 二级筛选 ----
        # type_id -> 子分类列表; 每个子分类含 key/name/value
        self.filters = {
            '1': [
                {'key': 'tid', 'name': '类型', 'value': [
                    {'n': '全部', 'v': '1'},
                    {'n': '动作片', 'v': '6'}, {'n': '爱情片', 'v': '7'}, {'n': '科幻片', 'v': '8'},
                    {'n': '恐怖片', 'v': '9'}, {'n': '战争片', 'v': '10'}, {'n': '喜剧片', 'v': '11'},
                    {'n': '剧情片', 'v': '12'}, {'n': '惊悚片', 'v': '20'}, {'n': '恋爱片', 'v': '21'},
                    {'n': '悬疑片', 'v': '22'}, {'n': '奇幻片', 'v': '23'}, {'n': '纪实片', 'v': '24'},
                    {'n': '军事片', 'v': '25'}, {'n': '犯罪片', 'v': '26'},
                ]},
                {'key': 'year', 'name': '年份', 'value': self._year_list()},
                {'key': 'lang', 'name': '语言', 'value': self._lang_list()},
                {'key': 'letter', 'name': '字母', 'value': self._letter_list()},
            ],
            '2': [
                {'key': 'tid', 'name': '类型', 'value': [
                    {'n': '全部', 'v': '2'},
                    {'n': '大陆剧', 'v': '30'}, {'n': '韩剧', 'v': '15'}, {'n': '美剧', 'v': '14'},
                    {'n': '港剧', 'v': '13'}, {'n': '日剧', 'v': '16'}, {'n': '台剧', 'v': '27'},
                    {'n': '泰剧', 'v': '28'},
                ]},
                {'key': 'year', 'name': '年份', 'value': self._year_list()},
                {'key': 'lang', 'name': '语言', 'value': self._lang_list()},
                {'key': 'letter', 'name': '字母', 'value': self._letter_list()},
            ],
            '5': [
                {'key': 'tid', 'name': '类型', 'value': [
                    {'n': '全部', 'v': '5'},
                    {'n': '大陆动漫', 'v': '17'}, {'n': '日本动漫', 'v': '47'}, {'n': '欧美动漫', 'v': '49'},
                    {'n': '香港动漫', 'v': '18'}, {'n': '韩国动漫', 'v': '48'}, {'n': '台湾动漫', 'v': '46'},
                ]},
                {'key': 'year', 'name': '年份', 'value': self._year_list()},
                {'key': 'lang', 'name': '语言', 'value': self._lang_list()},
                {'key': 'letter', 'name': '字母', 'value': self._letter_list()},
            ],
            '29': [
                {'key': 'tid', 'name': '类型', 'value': [
                    {'n': '全部', 'v': '29'},
                    {'n': '总裁短剧', 'v': '52'}, {'n': '神豪短剧', 'v': '53'}, {'n': '穿越重生短剧', 'v': '54'},
                    {'n': '都市短剧', 'v': '55'}, {'n': '年代短剧', 'v': '56'}, {'n': '长篇短剧', 'v': '57'},
                ]},
                {'key': 'year', 'name': '年份', 'value': self._year_list()},
                {'key': 'lang', 'name': '语言', 'value': self._lang_list()},
                {'key': 'letter', 'name': '字母', 'value': self._letter_list()},
            ],
            '37': [
                {'key': 'tid', 'name': '类型', 'value': [
                    {'n': '全部', 'v': '37'},
                    {'n': '大陆综艺', 'v': '38'}, {'n': '欧美综艺', 'v': '43'}, {'n': '香港综艺', 'v': '39'},
                    {'n': '台湾综艺', 'v': '40'}, {'n': '日本综艺', 'v': '41'}, {'n': '韩国综艺', 'v': '42'},
                ]},
                {'key': 'year', 'name': '年份', 'value': self._year_list()},
                {'key': 'lang', 'name': '语言', 'value': self._lang_list()},
                {'key': 'letter', 'name': '字母', 'value': self._letter_list()},
            ],
        }

    # ===================== 工具方法 =====================
    @staticmethod
    def _year_list():
        """年份按当前年份动态生成，避免跨年后筛选里没有新年份"""
        now_year = datetime.date.today().year
        items = [{'n': '全部', 'v': ''}]
        for y in range(now_year, now_year - 23, -1):
            items.append({'n': str(y), 'v': str(y)})
        return items

    @staticmethod
    def _lang_list():
        return [
            {'n': '全部', 'v': ''}, {'n': '国语', 'v': '国语'}, {'n': '英语', 'v': '英语'},
            {'n': '粤语', 'v': '粤语'}, {'n': '闽南语', 'v': '闽南语'}, {'n': '韩语', 'v': '韩语'},
            {'n': '日语', 'v': '日语'}, {'n': '其它', 'v': '其它'},
        ]

    @staticmethod
    def _letter_list():
        items = [{'n': '全部', 'v': ''}]
        for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
            items.append({'n': c, 'v': c})
        items.append({'n': '0-9', 'v': '0-9'})
        return items

    def _abs_url(self, url):
        """相对路径补成绝对地址，站点部分封面走 /img.php?url= 代理"""
        if not url:
            return ''
        url = url.strip()
        if url.startswith('//'):
            return 'https:' + url
        if url.startswith('http://') or url.startswith('https://'):
            return url
        if url.startswith('/'):
            return self.site_url + url
        return self.site_url + '/' + url

    def _fetch(self, path, retries=2):
        """带重试的页面抓取，提升加载稳定性"""
        url = self.site_url + path if path.startswith('/') else path
        headers = dict(self.headers)
        headers['Referer'] = self.site_url + '/'
        for i in range(retries + 1):
            try:
                resp = self.fetch(url, headers=headers)
                if resp:
                    return resp.text
            except Exception:
                pass
        return ''

    def _decode(self, text):
        """HTML 实体解码"""
        if not text:
            return ''
        text = text.replace('&nbsp;', ' ').replace('&amp;', '&')
        text = text.replace('&lt;', '<').replace('&gt;', '>')
        text = text.replace('&quot;', '"').replace('&#39;', "'")
        return text.strip()

    @staticmethod
    def _strip_tags(text):
        if not text:
            return ''
        return re.sub(r'<[^>]*>', '', text)

    def _re(self, pattern, text, default=''):
        """正则搜索，取第一个分组或整个匹配"""
        m = re.search(pattern, text)
        if not m:
            return default
        return m.group(1) if m.lastindex else m.group(0)

    def _clean_text(self, text):
        """去标签 + 实体解码 + 压缩空白"""
        text = self._decode(self._strip_tags(text))
        return re.sub(r'\s+', ' ', text).strip()

    def _join_names(self, text):
        """演员/导演等多人字段统一成逗号分隔"""
        text = self._clean_text(text)
        if not text:
            return ''
        if ',' in text or '，' in text:
            return text.strip(' ,，')
        parts = [p for p in text.split(' ') if p]
        return ','.join(parts)

    @staticmethod
    def _total_page(html, default=0):
        """读分页条上的 当前页/总页数"""
        m = re.search(r'<span class="num">\s*\d+\s*/\s*(\d+)\s*</span>', html)
        if m:
            try:
                return int(m.group(1))
            except (TypeError, ValueError):
                return default
        return default

    @staticmethod
    def _norm_extend(extend):
        """兼容 Hiker 传 dict 或 JSON 字符串两种情况"""
        if not extend:
            return {}
        if isinstance(extend, dict):
            return extend
        if isinstance(extend, str):
            try:
                data = json.loads(extend)
                if isinstance(data, dict):
                    return data
            except (TypeError, ValueError):
                return {}
        return {}

    # ===================== 卡片解析 =====================
    def _parse_card(self, html_block):
        """从首页/分类列表的 <li> 块中解析视频卡片"""
        vid = self._re(r'href="/detail/(\d+)\.html"', html_block)
        if not vid:
            return None
        name = self._re(r'title="([^"]+)"', html_block)
        pic = self._re(r'data-original="([^"]+)"', html_block)
        remark = self._re(r'class="pic-text[^"]*"[^>]*>([^<]+)<', html_block)
        score = self._re(r'class="pic-tag[^"]*"[^>]*>([^<]+)<', html_block)
        # 列表页的简介/演员信息
        actor = ''
        p_match = re.search(r'<p class="text[^"]*"[^>]*>([^<]+)<', html_block)
        if p_match:
            actor = p_match.group(1).strip()
        return {
            'vod_id': vid,
            'vod_name': self._decode(name),
            'vod_pic': self._abs_url(pic) if pic else self.default_pic,
            'vod_remarks': self._decode(remark),
            'vod_score': self._decode(score),
            'vod_actor': self._decode(actor),
        }

    def _parse_list_cards(self, html):
        """批量解析列表页的视频卡片"""
        pattern = r'<li[^>]+class="[^"]*col-md-6[^"]*"[^>]*>(.*?)</li>'
        blocks = re.findall(pattern, html, re.DOTALL)
        videos = []
        seen = set()
        for block in blocks:
            card = self._parse_card(block)
            if card and card['vod_id'] not in seen:
                seen.add(card['vod_id'])
                videos.append(card)
        return videos

    def _parse_search_cards(self, html):
        """解析搜索结果页的视频卡片（列表式布局）"""
        pattern = r'<li[^>]+class="[^"]*active[^"]*clearfix"[^>]*>(.*?)</li>'
        blocks = re.findall(pattern, html, re.DOTALL)
        videos = []
        seen = set()
        for block in blocks:
            vid = self._re(r'href="/detail/(\d+)\.html"', block)
            if not vid or vid in seen:
                continue
            seen.add(vid)
            name = self._re(r'title="([^"]+)"', block)
            pic = self._re(r'data-original="([^"]+)"', block)
            remark = self._re(r'class="pic-text[^"]*"[^>]*>([^<]+)<', block)
            # 搜索结果页的结构化信息
            director = self._re(r'导演：</span>([^<]+)', block)
            actor = self._re(r'主演：</span>([^<]+)', block)
            type_name = self._re(r'类型：</span>([^<]+)', block)
            area = self._re(r'地区：</span>([^<]+)', block)
            year = self._re(r'年份：</span>([^<]+)', block)
            videos.append({
                'vod_id': vid,
                'vod_name': self._decode(name),
                'vod_pic': self._abs_url(pic) if pic else self.default_pic,
                'vod_remarks': self._decode(remark),
                'vod_director': self._decode(director),
                'vod_actor': self._decode(actor),
                'vod_type': self._decode(type_name),
                'vod_area': self._decode(area),
                'vod_year': self._decode(year),
            })
        return videos

    # ===================== 构建筛选路径 =====================
    def _build_show_path(self, tid, extend, page):
        """分类列表 URL: 各筛选段依次拼接（旧写法是覆盖式，只有最后一个生效）"""
        ext = self._norm_extend(extend)
        sub_tid = str(ext.get('tid') or tid or '1').strip()
        segs = ['/show/' + sub_tid]
        year = str(ext.get('year') or '').strip()
        lang = str(ext.get('lang') or '').strip()
        letter = str(ext.get('letter') or '').strip()
        if year:
            segs.append('/year/' + urllib.parse.quote(year, safe=''))
        if lang:
            segs.append('/lang/' + urllib.parse.quote(lang, safe=''))
        if letter:
            segs.append('/letter/' + urllib.parse.quote(letter, safe=''))
        try:
            page_no = int(page)
        except (TypeError, ValueError):
            page_no = 1
        if page_no > 1:
            segs.append('/page/' + str(page_no))
        return ''.join(segs) + '.html'

    # ===================== 详情页: 线路与剧集 =====================
    def _line_name_before(self, html, pos):
        """取指定位置上方最近的 h3 标题作为线路名"""
        matches = list(re.finditer(r'<h3[^>]*>(.*?)</h3>', html[:pos], re.DOTALL))
        for m in reversed(matches):
            name = self._clean_text(m.group(1))
            if not name:
                continue
            if any(bad in name for bad in ('简介', '榜单', '猜你', '评论', '下载', '排行')):
                continue
            return name
        return ''

    def _parse_play_lines(self, html, vid):
        """以播放列表容器为顺序来源，线路名取其上方最近的 h3，集数按集号排序"""
        vid_pat = re.escape(str(vid))
        ep_in_block = re.compile(
            r'<a[^>]*href="(/play/' + vid_pat + r'_(\d+)_(\d+)\.html)"[^>]*>(.*?)</a>',
            re.DOTALL)
        boiler = ('立即播放', '立即观看', '播放', '查看详情', '详情')

        play_from = []
        play_url = []

        # 主线: 每个 <ul class="stui-content__playlist"> 就是一条线路，顺序即页面顺序
        for block in re.finditer(
                r'<ul[^>]*class="[^"]*stui-content__playlist[^"]*"[^>]*>(.*?)</ul>', html, re.DOTALL):
            line_name = self._line_name_before(html, block.start())
            episodes = {}
            for m in ep_in_block.finditer(block.group(1)):
                sid, nid = m.group(2), m.group(3)
                name = self._clean_text(m.group(4))
                if name in boiler:
                    name = ''
                if nid not in episodes or (not episodes[nid][0] and name):
                    episodes[nid] = (name, sid)
            if not episodes:
                continue
            keys = sorted(episodes.keys(), key=lambda x: int(x))
            items = []
            for nid in keys:
                name, sid = episodes[nid]
                label = name or ('第{0}集'.format(nid))
                items.append('{0}${1}_{2}_{3}.html'.format(label, vid, sid, nid))
            play_from.append(line_name or ('线路' + episodes[keys[0]][1]))
            play_url.append('#'.join(items))

        # 兜底: 页面结构不是标准面包模板时，按线路号分组，顺序取首次出现顺序
        if not play_from:
            groups = {}
            order = []
            for m in ep_in_block.finditer(html):
                sid, nid = m.group(2), m.group(3)
                if sid not in groups:
                    groups[sid] = {}
                    order.append(sid)
                name = self._clean_text(m.group(4))
                if name in boiler:
                    name = ''
                if nid not in groups[sid] or (not groups[sid][nid][0] and name):
                    groups[sid][nid] = (name, sid)
            for sid in order:
                episodes = groups[sid]
                items = []
                for nid in sorted(episodes.keys(), key=lambda x: int(x)):
                    label = episodes[nid][0] or ('第{0}集'.format(nid))
                    items.append('{0}${1}_{2}_{3}.html'.format(label, vid, sid, nid))
                play_from.append('线路' + sid)
                play_url.append('#'.join(items))
        return play_from, play_url

    def _detail_field(self, html, label):
        """详情页 <p class="data"><span>标签：</span>值</p>"""
        m = re.search(r'<p[^>]*>\s*<span[^>]*>' + label + r'：</span>(.*?)</p>', html, re.DOTALL)
        if not m:
            m = re.search(label + r'：</span>(.*?)</p>', html, re.DOTALL)
        return self._join_names(m.group(1)) if m else ''

    def detailContent(self, ids):
        """详情页: 解析影片信息 + 多线路播放列表"""
        if not ids:
            return {'list': []}
        vid = str(ids[0]).strip()
        html = self._fetch('/detail/{0}.html'.format(vid))
        if not html:
            return {'list': []}

        title = self._re(r'<h1 class="title">([^<]+)</h1>', html)
        if not title:
            title = self._re(r'<title>([^_<]+)', html)

        pic = self._re(r'<div class="stui-content__thumb">.*?data-original="([^"]+)"', html) or \
            self._re(r'data-original="([^"]+)"', html)
        pic = self._abs_url(pic) or self.default_pic

        actor = self._detail_field(html, '主演')
        director = self._detail_field(html, '导演')
        vod_class = self._detail_field(html, '类型')
        if not vod_class:
            # 面包模板详情页没有「类型」行，用顶部导航高亮的栏目兜底
            vod_class = self._decode(self._re(
                r'<li class="active"><a href="/type/\d+\.html">([^<]+)</a></li>', html))
        area = self._detail_field(html, '地区')
        year = self._detail_field(html, '年份')

        # 简介: 优先取 #desc 的完整段落，其次取头部一行简介（跨行也能取全）
        desc = ''
        m = re.search(r'id="desc".*?<div class="stui-pannel_bd">\s*<p[^>]*>(.*?)</p>', html, re.DOTALL)
        if m:
            desc = m.group(1)
        if not desc:
            m = re.search(r'简介[：:]\s*</span>(.*?)(?:<a href="#desc"|</p>)', html, re.DOTALL)
            if m:
                desc = m.group(1)
        desc = self._clean_text(desc)

        play_from, play_url = self._parse_play_lines(html, vid)
        if not play_from:
            # 兜底: 用「立即播放」按钮的地址；再不行交给 playerContent 现查
            m = re.search(r'<a[^>]*href="(/play/[^"]+\.html)"[^>]*class="[^"]*btn[^"]*"', html)
            if not m:
                m = re.search(r'class="[^"]*btn[^"]*"[^>]*href="(/play/[^"]+\.html)"', html)
            if m:
                play_from.append('默认线路')
                play_url.append('正片${0}'.format(m.group(1).lstrip('/')[len('play/'):]))
            else:
                play_from.append('默认线路')
                play_url.append('正片$detail:{0}'.format(vid))

        result = [{
            'vod_id': vid,
            'vod_name': self._decode(title),
            'vod_pic': pic,
            'vod_content': desc,
            'vod_actor': actor,
            'vod_director': director,
            'vod_year': year,
            'vod_area': area,
            'vod_type': vod_class,
            'vod_play_from': '$$$'.join(play_from),
            'vod_play_url': '$$$'.join(play_url),
        }]
        return {'list': result}

    # ===================== 播放 =====================
    @staticmethod
    def _extract_braced_json(html, marker):
        """按括号配对取 JSON，容忍 </script> 之外的收尾差异"""
        idx = html.find(marker)
        while idx != -1:
            start = html.find('{', idx)
            if start == -1:
                return ''
            depth = 0
            in_str = False
            esc = False
            for i in range(start, len(html)):
                ch = html[i]
                if in_str:
                    if esc:
                        esc = False
                    elif ch == '\\':
                        esc = True
                    elif ch == '"':
                        in_str = False
                    continue
                if ch == '"':
                    in_str = True
                elif ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0:
                        return html[start:i + 1]
            idx = html.find(marker, idx + 1)
        return ''

    @staticmethod
    def _pad_b64(text):
        text = text.strip()
        pad = len(text) % 4
        if pad:
            text += '=' * (4 - pad)
        return text

    def _decode_play_url(self, url, encrypt):
        url = url.replace('\\/', '/').strip()
        if encrypt in (1, 2):
            raw = ''
            for candidate in (self._pad_b64(url), self._pad_b64(url.replace('-', '+').replace('_', '/'))):
                try:
                    raw = base64.b64decode(candidate).decode('utf-8', 'ignore')
                except Exception:
                    raw = ''
                if raw:
                    break
            if encrypt == 2:
                raw = raw[::-1]
            if raw:
                url = raw
        if encrypt in (1, 2) and '%' in url:
            try:
                url = urllib.parse.unquote(url)
            except Exception:
                pass
        if url.startswith('//'):
            url = 'https:' + url
        return url.strip()

    @staticmethod
    def _is_direct_media(url):
        """m3u8/mp4 等直链判定，只看路径不看查询串，避免把播放器页当成直链"""
        if not url.lower().startswith('http'):
            return False
        path = url.split('?')[0].split('#')[0].lower()
        for ext in ('.m3u8', '.m3u', '.mp4', '.flv', '.avi', '.mkv', '.m4a', '.mp3', '.ts'):
            if path.endswith(ext):
                return True
        return False

    def _play_headers(self):
        return {
            'User-Agent': self.headers['User-Agent'],
            'Referer': self.site_url + '/',
        }

    def _resolve_detail_play(self, vid):
        """兜底: 从详情页找「立即播放」或任意一条 /play/ 地址"""
        html = self._fetch('/detail/{0}.html'.format(vid))
        if not html:
            return ''
        m = re.search(r'<a[^>]*href="(/play/[^"]+\.html)"[^>]*class="[^"]*btn[^"]*"', html)
        if not m:
            m = re.search(r'class="[^"]*btn[^"]*"[^>]*href="(/play/[^"]+\.html)"', html)
        if not m:
            m = re.search(r'href="(/play/' + re.escape(str(vid)) + r'_\d+_\d+\.html)"', html)
        return m.group(1) if m else ''

    def playerContent(self, flag, id, vipFlags):
        """播放解析: 从播放页提取 m3u8/mp4 直链"""
        play_id = (id or '').strip()
        if not play_id:
            return {'parse': 1, 'url': self.site_url + '/', 'header': self.headers}

        # 兼容旧版兜底值: 播放$/detail/{vid}
        if play_id.startswith('detail:'):
            play_id = self._resolve_detail_play(play_id.split(':', 1)[1])
        elif '/detail/' in play_id:
            m = re.search(r'/detail/(\d+)', play_id)
            play_id = self._resolve_detail_play(m.group(1)) if m else ''

        if not play_id:
            return {'parse': 1, 'url': self.site_url + '/', 'header': self.headers}

        if play_id.startswith('http://') or play_id.startswith('https://'):
            page_url = play_id
        elif play_id.startswith('/'):
            page_url = self.site_url + play_id
        else:
            page_url = self.site_url + '/play/' + play_id.lstrip('/')

        html = self._fetch(page_url)
        if not html:
            return {'parse': 1, 'url': page_url, 'header': self._play_headers()}

        # 提取 var player_aaaa={...} JSON（正则 + 括号配对双保险）
        player_json = self._re(r'var\s+player_aaaa\s*=\s*(\{.*?\})\s*</script>', html)
        if not player_json:
            player_json = self._extract_braced_json(html, 'player_aaaa')

        player_data = {}
        if player_json:
            try:
                player_data = json.loads(player_json)
            except (ValueError, TypeError):
                player_data = {}
        if not isinstance(player_data, dict):
            player_data = {}

        url = str(player_data.get('url') or '').strip()
        try:
            encrypt = int(player_data.get('encrypt') or 0)
        except (TypeError, ValueError):
            encrypt = 0
        if url:
            url = self._decode_play_url(url, encrypt)

        if url and self._is_direct_media(url):
            return {'parse': 0, 'url': url, 'header': self._play_headers()}

        # 非直链: 交给播放器嗅探
        if url.startswith('http'):
            return {'parse': 1, 'url': url, 'header': self._play_headers()}

        iframe_src = self._re(r'<iframe[^>]+src="([^"]+)"', html)
        if iframe_src and iframe_src.startswith('http'):
            return {'parse': 1, 'url': iframe_src, 'header': self._play_headers()}

        return {'parse': 1, 'url': page_url, 'header': self._play_headers()}

    # ===================== Spider 标准接口 =====================

    def homeContent(self, filter):
        """首页内容 + 分类 + 筛选"""
        html = self._fetch('/')
        categories = [{'type_id': k, 'type_name': v} for k, v in self.categories.items()]
        videos = self._parse_list_cards(html)
        filters = self.filters
        return {'class': categories, 'list': videos[:30], 'filters': filters}

    def homeVideoContent(self):
        """首页推荐视频"""
        html = self._fetch('/')
        videos = self._parse_list_cards(html)
        return {'list': videos[:30]}

    def categoryContent(self, tid, pg, filter, extend):
        """分类页内容，支持二级筛选"""
        try:
            page = int(pg) if pg else 1
        except (TypeError, ValueError):
            page = 1
        path = self._build_show_path(tid, extend, page)
        html = self._fetch(path)
        videos = self._parse_list_cards(html)
        limit = 36
        pagecount = self._total_page(html, 0)
        if not pagecount:
            pagecount = page + 1 if len(videos) >= limit else page
        return {
            'list': videos,
            'page': page,
            'pagecount': pagecount,
            'limit': limit,
            'total': len(videos),
        }

    def searchContent(self, key, quick, pg='1'):
        """搜索"""
        try:
            page = int(pg) if pg else 1
        except (TypeError, ValueError):
            page = 1
        keyword = urllib.parse.quote((key or '').strip())
        if page > 1:
            path = '/search/page/{0}/wd/{1}.html'.format(page, keyword)
        else:
            path = '/search.html?wd={0}'.format(keyword)
        html = self._fetch(path)
        videos = self._parse_search_cards(html)
        limit = 10
        pagecount = self._total_page(html, 0)
        if not pagecount:
            pagecount = page + 1 if len(videos) >= limit else page
        return {
            'list': videos,
            'page': page,
            'pagecount': pagecount,
            'limit': limit,
            'total': len(videos),
        }
