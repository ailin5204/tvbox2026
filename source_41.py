# coding=utf-8
"""
目标站: 爱看机器人 (ikanbot.com)
模板: ikanbot 聚合搜索适配版
站点类型: 影视聚合搜索 / 爬虫播放
核心逻辑: 逆向 JS token 算法，调用 /api/getResN 获取真实 m3u8 播放地址
"""
import re
import sys
import json
import urllib.parse

sys.path.append('..')
from base.spider import Spider


class Spider(Spider):
    def init(self, extend=""):
        self.site_url = "https://ikanbot.com"
        self.headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
            'Accept-Language': 'zh-CN,zh;q=0.9',
            'Referer': self.site_url + "/",
        }
        self.default_pic = "https://pic.rmb.bdstatic.com/bjh/user/default.png"

    # ========== 工具方法 ==========
    def _fix_url(self, url):
        if not url:
            return ""
        url = url.strip()
        if url.startswith("//"):
            return "https:" + url
        if not url.startswith("http"):
            return urllib.parse.urljoin(self.site_url, url)
        return url

    def _fix_cover(self, pic):
        """封面图 URL 处理：拼 @Referer 绕过豆瓣防盗链"""
        if not pic or pic.startswith("data:"):
            return self.default_pic
        url = self._fix_url(pic)
        # OK影视(FongMi) 加载图片时解析 URL 末尾的 @Referer=xxx
        return url + "@Referer=" + urllib.parse.quote("https://movie.douban.com/", safe="")

    def _calc_tks(self, current_id, e_token):
        """
        逆向页面 JS 的 get_tks() 函数：
        取 current_id 后4位，每位 digit % 3 + 1 作为偏移量，
        从 e_token 中截取 8 位字符，拼接成 v_tks
        """
        if not current_id or not e_token:
            return ""
        last4 = str(current_id)[-4:]
        result = []
        token = e_token
        for ch in last4:
            digit = int(ch)
            offset = digit % 3 + 1
            result.append(token[offset:offset + 8])
            token = token[offset + 8:]
        return "".join(result)

    # flag -> 真实来源名称映射表
    FLAG_NAME_MAP = {
        "jsm3u8": "极速",
        "bfzym3u8": "暴风资源",
        "ffm3u8": "飞速",
        "iqym3u8": "爱奇艺",
        "dyttm3u8": "电影天堂",
        "1080zyk": "1080资源库",
        "360zy": "360资源",
        "jinyingm3u8": "金鹰",
        "zuidam3u8": "最大资源",
        "tym3u8": "天翼",
        "ukm3u8": "U酷",
        "kcm3u8": "快车",
        "lzm3u8": "梨园",
        "hym3u8": "红颜",
        "snm3u8": "思古",
        "wjm3u8": "无尽",
        "hhm3u8": "樱花",
        "dbm3u8": "大白",
        "ikm3u8": "爱看",
        "subm3u8": "迅播",
        "okm3u8": "OK资源",
        "yym3u8": "速播",
        "nnm3u8": "牛牛",
        "gsm3u8": "高速",
        "xlm3u8": "西蓝",
        "sdm3u8": "速达",
        "rym3u8": "日野",
        "mtm3u8": "暴风",
        "yhm3u8": "樱花",
    }

    def _get_play_data(self, vid, mtype, token):
        """
        调用 /api/getResN 获取真实播放线路
        返回: (play_from_list, play_url_list)
        使用 resData 中的 flag 字段作为真实线路名称
        """
        tks = self._calc_tks(vid, token)
        api_url = f"{self.site_url}/api/getResN?videoId={vid}&mtype={mtype}&token={tks}"
        try:
            resp = self.fetch(api_url, headers=self.headers)
            if not resp:
                return [], []
            data = json.loads(resp.text)
            if data.get("state") != 1:
                return [], []
            data_list = data.get("data", {}).get("list", [])
            play_from = []
            play_url = []
            name_counter = {}
            for idx, item in enumerate(data_list):
                try:
                    res_arr = json.loads(item.get("resData", "[]"))
                except Exception:
                    continue
                # 从 resData 中提取 flag 作为真实线路名称
                line_name = "线路" + str(idx + 1)
                if res_arr:
                    flag = res_arr[0].get("flag", "")
                    if flag:
                        line_name = self.FLAG_NAME_MAP.get(flag, flag)
                # 处理重名：同名线路追加序号
                if line_name in name_counter:
                    name_counter[line_name] += 1
                    line_name = f"{line_name}{name_counter[line_name]}"
                else:
                    name_counter[line_name] = 1
                ep_list = []
                for res_item in res_arr:
                    url_str = res_item.get("url", "")
                    if not url_str:
                        continue
                    for part in url_str.split("#"):
                        part = part.strip()
                        if "$" in part:
                            ep_list.append(part)
                if ep_list:
                    play_from.append(line_name)
                    play_url.append("#".join(ep_list))
            return play_from, play_url
        except Exception:
            return [], []

    def _extract_videos(self, html):
        """从 HTML 中提取视频列表（首页/分类通用）"""
        videos = []
        items = re.findall(
            r'<a[^>]+href="(/play/(\d+))"[^>]*>.*?<img[^>]*alt="([^"]*)"[^>]*data-src="([^"]*)"[^>]*>.*?<p[^>]*>([^<]*)</p>.*?</a>',
            html, re.DOTALL
        )
        seen = set()
        for href, vid, alt, pic, p_text in items:
            if vid in seen:
                continue
            seen.add(vid)
            name = alt.strip() if alt.strip() else p_text.strip()
            if not name:
                name = vid
            videos.append({
                "vod_id": vid,
                "vod_name": name,
                "vod_pic": self._fix_cover(pic),
                "vod_remarks": ""
            })
        return videos

    def _extract_billboard(self, html):
        """解析榜单页 /billboard.html — 使用 split 分块避免正则截断问题"""
        videos = []
        parts = html.split('<div class="item result-info')
        seen = set()
        for part in parts[1:]:
            block = part.split('<div class="clearfix">')[0]
            href = re.search(r'href="/play/(\d+)"', block)
            if not href:
                continue
            vid = href.group(1)
            if vid in seen:
                continue
            seen.add(vid)

            rank = re.search(r'<h3[^>]*>\s*(\d+)\s*</h3>', block)
            rank = rank.group(1) if rank else ""

            title = re.search(r'alt="([^"]*)"', block)
            title = title.group(1) if title else vid

            # 优先 data-src，其次 src（排除 SVG 占位符）
            pic = ""
            pic_match = re.search(r'data-src="([^"]+)"', block)
            if pic_match:
                pic = pic_match.group(1)
            else:
                pic_match = re.search(r'src="([^"]+)"', block)
                if pic_match:
                    pic = pic_match.group(1)
                    if pic.startswith("data:image/svg") or pic.startswith("data:image/gif"):
                        pic = ""

            videos.append({
                "vod_id": vid,
                "vod_name": title,
                "vod_pic": self._fix_cover(pic) if pic else self.default_pic,
                "vod_remarks": "第" + rank + "名" if rank else ""
            })
        return videos

    def _img_headers(self):
        """返回图片加载所需的请求头，解决豆瓣等防盗链问题"""
        return {"Referer": self.site_url + "/", "User-Agent": self.headers["User-Agent"]}

    # ========== 首页 ==========
    def homeContent(self, filter):
        categories = [
            {"type_id": "movie", "type_name": "电影"},
            {"type_id": "tv", "type_name": "剧集"},
            {"type_id": "billboard", "type_name": "榜单"},
        ]
        resp = self.fetch(self.site_url + "/", headers=self.headers)
        videos = self._extract_videos(resp.text) if resp else []
        return {"class": categories, "list": videos[:30], "filters": {}, "header": self._img_headers()}

    def homeVideoContent(self):
        return self.homeContent(False)

    # ========== 分类 ==========
    def categoryContent(self, tid, pg, filter, extend):
        page = int(pg) if pg else 1
        if tid == "movie":
            if page > 1:
                url = f"{self.site_url}/hot/index-movie-热门-p-{page}.html"
            else:
                url = f"{self.site_url}/hot/index-movie-热门.html"
        elif tid == "tv":
            if page > 1:
                url = f"{self.site_url}/hot/index-tv-热门-p-{page}.html"
            else:
                url = f"{self.site_url}/hot/index-tv-热门.html"
        elif tid == "billboard":
            url = f"{self.site_url}/billboard.html"
        else:
            url = self.site_url + "/"

        resp = self.fetch(url, headers=self.headers)
        videos = []
        if resp:
            if tid == "billboard":
                videos = self._extract_billboard(resp.text)
            else:
                videos = self._extract_videos(resp.text)

        return {
            "list": videos,
            "page": page,
            "pagecount": 9999,
            "limit": 30,
            "total": 0,
        }

    # ========== 搜索 ==========
    def searchContent(self, key, quick, pg="1"):
        page = int(pg) if pg else 1
        encoded = urllib.parse.quote(key)
        url = f"{self.site_url}/search?q={encoded}"
        resp = self.fetch(url, headers=self.headers)
        videos = []
        if resp:
            html = resp.text
            # 用 split 分割每个搜索结果块，避免正则嵌套 div 匹配问题
            parts = html.split('<div class="media">')
            seen = set()
            for part in parts[1:]:
                # 提取视频ID
                href = re.search(r'href="/play/(\d+)"', part)
                if not href:
                    continue
                vid = href.group(1)
                if vid in seen:
                    continue
                seen.add(vid)
                # 优先用 title-text 链接文本（含年份），其次用 alt 属性
                title = re.search(r'class="title-text"[^>]*>([^<]+)</a>', part)
                if title:
                    title = title.group(1).strip()
                else:
                    title = re.search(r'alt="([^"]*)"', part)
                    title = title.group(1).strip() if title else vid
                # 提取封面图
                pic = re.search(r'data-src="([^"]*)"', part)
                pic = self._fix_cover(pic.group(1)) if pic else self.default_pic
                videos.append({
                    "vod_id": vid,
                    "vod_name": title,
                    "vod_pic": pic,
                    "vod_remarks": ""
                })
        return {
            "list": videos,
            "page": page,
            "pagecount": 1,
            "limit": 30,
            "total": len(videos),
            "header": self._img_headers()
        }

    # ========== 详情 ==========
    def detailContent(self, ids):
        if not ids:
            return {"list": []}
        vid = ids[0]
        url = f"{self.site_url}/play/{vid}"
        resp = self.fetch(url, headers=self.headers)
        if not resp:
            return {"list": []}

        html = resp.text

        current_id = re.search(r'id="current_id"[^>]*value="(\d+)"', html)
        e_token = re.search(r'id="e_token"[^>]*value="([^"]+)"', html)
        mtype = re.search(r'id="mtype"[^>]*value="(\d+)"', html)

        cid = current_id.group(1) if current_id else vid
        tok = e_token.group(1) if e_token else ""
        mt = mtype.group(1) if mtype else "1"

        name = vid
        title_match = re.search(r'<h1[^>]*id="video_title"[^>]*>([^<]*)</h1>', html)
        if title_match:
            name = title_match.group(1).strip()

        pic = self.default_pic
        pic_match = re.search(r'<meta[^>]*property="og:image"[^>]*content="([^"]+)"', html)
        if pic_match:
            pic = self._fix_url(pic_match.group(1))
        else:
            pic_match = re.search(r'<img[^>]*class="[^"]*cover[^"]*"[^>]*data-src="([^"]+)"', html)
            if pic_match:
                pic = self._fix_url(pic_match.group(1))

        content = ""
        year = ""
        area = ""
        director = ""
        actor = ""
        meta_h3s = re.findall(r'<h3[^>]*class="[^"]*meta[^"]*"[^>]*>([^<]*)</h3>', html)
        if meta_h3s:
            content = meta_h3s[0].strip() if meta_h3s[0] else ""
            for h3 in meta_h3s:
                txt = h3.strip()
                if not txt:
                    continue
                m = re.search(r'^(\d{4})$', txt)
                if m and not year:
                    year = m.group(1)
                if re.search(r'^(中国|美国|韩国|日本|英国|法国|德国|泰国|印度|香港|台湾|大陆|欧美|海外)$', txt) and not area:
                    area = txt
                if (',' in txt or '，' in txt or '/' in txt) and len(txt) > 5 and not actor:
                    if '/' in txt:
                        parts = txt.split('/', 1)
                        director = parts[0].strip()
                        actor = parts[1].strip()
                    else:
                        actor = txt

        play_from, play_url = self._get_play_data(cid, mt, tok)
        if not play_url:
            play_from = ["默认线路"]
            play_url = [f"播放${url}"]

        result = [{
            "vod_id": vid,
            "vod_name": name,
            "vod_pic": self._fix_cover(pic),
            "vod_content": content,
            "vod_actor": actor,
            "vod_director": director,
            "vod_year": year,
            "vod_area": area,
            "vod_play_from": '$$$'.join(play_from),
            "vod_play_url": '$$$'.join(play_url)
        }]
        return {"list": result, "header": self._img_headers()}

    # ========== 播放 ==========
    def playerContent(self, flag, id, vipFlags):
        play_url = id
        if "$" in id:
            play_url = id.split("$")[-1]
        play_url = self._fix_url(play_url)

        if '.m3u8' in play_url or '.mp4' in play_url:
            return {
                "parse": 0,
                "url": play_url,
                "header": self.headers
            }
        return {
            "parse": 1,
            "url": play_url,
            "header": self.headers
        }
