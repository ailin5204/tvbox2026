# -*- coding: utf-8 -*-
"""
哈密瓜影院 TVBox/猫影视爬虫插件 — https://www.snow4all.com/
苹果CMS v10 (ewave模板) + JSON数据接口

数据接口:
  列表/分类    /index.php/ajax/data?mid=1&tid={type_id}&page={page}&limit=36
  筛选参数     &area={area}&year={year}&class={class}&lang={lang}
  搜索         /index.php/ajax/suggest?mid=1&wd={kw}&limit=20&page={page}
  详情页       /hamigua/{id}.html
  播放页       /hamiguaplay/{id}-{sid}-{nid}.html
  播放数据     var player_aaaa={"url":"真实m3u8地址","from":"线路名",...}
"""

import re
import json
import time
import warnings
import threading
from urllib.parse import quote

try:
    warnings.filterwarnings("ignore")
    import urllib3
    urllib3.disable_warnings()
except Exception:
    pass

try:
    from base.spider import Spider
except ImportError:
    import requests as _rq
    from requests.adapters import HTTPAdapter

    class Spider:
        def __init__(self):
            self._session = _rq.Session()
            adapter = HTTPAdapter(pool_connections=20, pool_maxsize=20)
            self._session.mount("http://", adapter)
            self._session.mount("https://", adapter)

        def fetch(self, url, headers=None, timeout=15, **kw):
            headers = headers or {}
            headers.setdefault("User-Agent", UA)
            return self._session.get(url, headers=headers, timeout=timeout, verify=False, **kw)

        def destroy(self):
            try:
                self._session.close()
            except Exception:
                pass


HOST = "https://www.snow4all.com"
UA = ("Mozilla/5.0 (Linux; Android 12; M2007J22C) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36")

CLASSES = [
    {"type_name": "电影", "type_id": "1"},
    {"type_name": "连续剧", "type_id": "2"},
    {"type_name": "综艺", "type_id": "3"},
    {"type_name": "动漫", "type_id": "4"},
    {"type_name": "短剧", "type_id": "5"},
]

SUB_CLASSES = {
    "1": [
        {"n": "喜剧片", "v": "6"},
        {"n": "动作片", "v": "7"},
        {"n": "爱情片", "v": "8"},
        {"n": "纪录片", "v": "45"},
        {"n": "电影解说", "v": "58"},
    ],
    "2": [
        {"n": "国产剧", "v": "13"},
        {"n": "港台剧", "v": "14"},
        {"n": "韩剧", "v": "15"},
        {"n": "欧美剧", "v": "16"},
        {"n": "日剧", "v": "46"},
    ],
    "3": [
        {"n": "大陆综艺", "v": "49"},
        {"n": "港台综艺", "v": "50"},
        {"n": "日韩综艺", "v": "51"},
    ],
    "4": [
        {"n": "国产动漫", "v": "53"},
        {"n": "日韩动漫", "v": "54"},
    ],
    "5": [
        {"n": "全部短剧", "v": "5"},
    ],
}

YEARS = [{"n": str(y), "v": str(y)} for y in range(2026, 2009, -1)]
YEARS.insert(0, {"n": "全部", "v": ""})

AREAS = [
    {"n": "全部", "v": ""},
    {"n": "大陆", "v": "大陆"},
    {"n": "香港", "v": "香港"},
    {"n": "台湾", "v": "台湾"},
    {"n": "美国", "v": "美国"},
    {"n": "韩国", "v": "韩国"},
    {"n": "日本", "v": "日本"},
    {"n": "泰国", "v": "泰国"},
    {"n": "英国", "v": "英国"},
    {"n": "法国", "v": "法国"},
    {"n": "德国", "v": "德国"},
    {"n": "意大利", "v": "意大利"},
    {"n": "西班牙", "v": "西班牙"},
    {"n": "印度", "v": "印度"},
    {"n": "加拿大", "v": "加拿大"},
    {"n": "其他", "v": "其他"},
]

LANGS = [
    {"n": "全部", "v": ""},
    {"n": "国语", "v": "国语"},
    {"n": "粤语", "v": "粤语"},
    {"n": "英语", "v": "英语"},
    {"n": "韩语", "v": "韩语"},
    {"n": "日语", "v": "日语"},
    {"n": "泰语", "v": "泰语"},
    {"n": "其他", "v": "其他"},
]

FILTERS = {}
for tid, subs in SUB_CLASSES.items():
    filters = []
    if len(subs) > 1 or subs[0]["n"] != "全部短剧":
        filters.append({
            "key": "class",
            "name": "类型",
            "value": [{"n": "全部", "v": ""}] + subs
        })
    if tid in ("1", "2", "4"):
        filters.append({"key": "area", "name": "地区", "value": AREAS})
    if tid == "3":
        filters.append({"key": "area", "name": "地区", "value": AREAS})
        filters.append({"key": "lang", "name": "语言", "value": LANGS})
    filters.append({"key": "year", "name": "年份", "value": YEARS})
    FILTERS[tid] = filters

LIST_PAGE_SIZE = 36
HOME_PAGE_SIZE = 18
LIST_CACHE_TTL = 60
DETAIL_CACHE_TTL = 300
HOME_CACHE_TTL = 30
SEARCH_CACHE_TTL = 30


def _urlencode(s):
    return quote(s or "", safe="")


def _strip(txt):
    return re.sub(r"\s+", " ", txt or "").strip()


def _build_vod(item):
    return {
        "vod_id": str(item.get("vod_id", "")),
        "vod_name": _strip(item.get("vod_name", "")),
        "vod_pic": item.get("vod_pic", ""),
        "vod_remarks": _strip(item.get("vod_remarks", "")),
        "vod_year": str(item.get("vod_year", "")),
        "vod_area": _strip(item.get("vod_area", "")),
        "vod_lang": _strip(item.get("vod_lang", "")),
        "vod_actor": _strip(item.get("vod_actor", "")),
        "vod_director": _strip(item.get("vod_director", "")),
        "vod_class": _strip(item.get("vod_class", "")),
        "vod_content": _strip(item.get("vod_content", ""))[:500],
    }


class Spider(Spider):
    _RE_PLAYER_JSON = re.compile(r'var\s+player_aaaa\s*=\s*(\{[\s\S]*?\})\s*</script>')
    _RE_PLAYER_JSON2 = re.compile(r'var\s+player_aaaa\s*=\s*(\{.*?\});')

    def getName(self):
        return "哈密瓜影院"

    def init(self, extend=""):
        self.header = {
            "User-Agent": UA,
            "Referer": HOST + "/",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
            "Accept-Encoding": "gzip, deflate",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
            "Connection": "keep-alive",
        }
        self.ajax_header = dict(self.header)
        self.ajax_header["X-Requested-With"] = "XMLHttpRequest"
        try:
            import requests
            from requests.adapters import HTTPAdapter
            self._session = requests.Session()
            adapter = HTTPAdapter(pool_connections=20, pool_maxsize=20)
            self._session.mount("http://", adapter)
            self._session.mount("https://", adapter)
            self._session.trust_env = False
        except Exception as e:
            print("[哈密瓜] requests 不可用, 回退到框架 fetch: " + str(e))
            self._session = None

        self._list_cache = {}
        self._detail_cache = {}
        self._home_cache = None
        self._search_cache = {}
        self._source_name_cache = {}
        self._cache_lock = threading.Lock()

    def isVideoFormat(self, url):
        u = (url or "").lower().rstrip("?#")
        return any(u.endswith(ext) for ext in (".m3u8", ".mp4", ".flv", ".ts"))

    def destroy(self):
        sess = getattr(self, "_session", None)
        if sess is not None:
            try:
                sess.close()
            except Exception:
                pass

    def _http_get(self, url, timeout=8, use_ajax=False):
        headers = self.ajax_header if use_ajax else self.header
        sess = getattr(self, "_session", None)
        if sess is not None and hasattr(sess, "get"):
            try:
                rsp = sess.get(url, headers=headers, timeout=timeout, verify=False)
                if getattr(rsp, "status_code", 0) == 200:
                    txt = getattr(rsp, "text", None) or ""
                    if txt:
                        return txt
            except Exception:
                pass
        try:
            rsp = self.fetch(url, headers=headers, timeout=timeout)
            if getattr(rsp, "status_code", 0) == 200:
                txt = getattr(rsp, "text", None) or ""
                if txt:
                    return txt
        except Exception:
            pass
        return ""

    def _http_get_json(self, url, timeout=8):
        html = self._http_get(url, timeout=timeout, use_ajax=True)
        if not html:
            return None
        try:
            return json.loads(html)
        except Exception:
            return None

    def homeContent(self, filter):
        return {"class": CLASSES, "filters": FILTERS}

    def homeVideoContent(self):
        now = time.time()
        with self._cache_lock:
            if self._home_cache:
                ts, payload = self._home_cache
                if now - ts < HOME_CACHE_TTL:
                    return payload

        videos = []
        seen = set()
        # 只取3个热门分类，减少请求
        for tid in ("1", "2", "4"):
            url = HOST + "/index.php/ajax/data?mid=1&tid=" + tid + "&page=1&limit=12"
            data = self._http_get_json(url, timeout=6)
            if data and data.get("list"):
                for item in data["list"]:
                    vid = str(item.get("vod_id", ""))
                    if not vid or vid in seen:
                        continue
                    seen.add(vid)
                    videos.append(_build_vod(item))
                    if len(videos) >= HOME_PAGE_SIZE:
                        break
            if len(videos) >= HOME_PAGE_SIZE:
                break

        payload = {"list": videos[:HOME_PAGE_SIZE]}
        with self._cache_lock:
            self._home_cache = (now, payload)
        return payload

    def categoryContent(self, tid, pg, filter, extend):
        try:
            page = int(pg or 1)
            if page < 1:
                page = 1
            ext = extend or {}
            cls = str(ext.get("class", "") or "")
            area = str(ext.get("area", "") or "")
            year = str(ext.get("year", "") or "")
            lang = str(ext.get("lang", "") or "")

            use_tid = cls if cls else str(tid)

            cache_key = (use_tid, area, year, lang, page)
            now = time.time()
            with self._cache_lock:
                hit = self._list_cache.get(cache_key)
                if hit and now - hit[0] < LIST_CACHE_TTL:
                    return hit[1]

            url = HOST + "/index.php/ajax/data?mid=1&tid=" + use_tid + "&page=" + str(page) + "&limit=" + str(LIST_PAGE_SIZE)
            if area:
                url += "&area=" + _urlencode(area)
            if year:
                url += "&year=" + _urlencode(year)
            if lang:
                url += "&lang=" + _urlencode(lang)

            data = self._http_get_json(url, timeout=6)
            if not data or not data.get("list"):
                return {"list": [], "page": page, "pagecount": 1, "limit": LIST_PAGE_SIZE, "total": 0}

            videos = []
            for item in data["list"]:
                videos.append(_build_vod(item))

            pagecount = data.get("pagecount", 1) or 1
            total = data.get("total", 0) or 0

            payload = {
                "list": videos,
                "page": page,
                "pagecount": pagecount,
                "limit": len(videos) or LIST_PAGE_SIZE,
                "total": total,
            }
            with self._cache_lock:
                self._list_cache[cache_key] = (now, payload)
            return payload
        except Exception as e:
            print("[哈密瓜] categoryContent 异常: " + str(e))
            return {"list": [], "page": 1, "pagecount": 1, "limit": LIST_PAGE_SIZE, "total": 0}

    def detailContent(self, ids):
        try:
            if isinstance(ids, (list, tuple)):
                ids = ids[0]
            vod_id = str(ids)
            now = time.time()
            with self._cache_lock:
                hit = self._detail_cache.get(vod_id)
                if hit and now - hit[0] < DETAIL_CACHE_TTL:
                    return hit[1]

            # 1. 从ajax/data获取完整信息（一次请求，包含所有字段）
            url = HOST + "/index.php/ajax/data?mid=1&tid=1&page=1&limit=1&ids=" + vod_id
            data = self._http_get_json(url, timeout=7)
            vod = None
            if data and data.get("list"):
                for item in data["list"]:
                    if str(item.get("vod_id")) == vod_id:
                        vod = _build_vod(item)
                        break

            if not vod:
                vod = {
                    "vod_id": vod_id,
                    "vod_name": "",
                    "vod_pic": "",
                    "vod_year": "",
                    "vod_area": "",
                    "vod_lang": "",
                    "vod_remarks": "",
                    "vod_actor": "",
                    "vod_director": "",
                    "vod_class": "",
                    "vod_content": "",
                    "vod_play_from": "",
                    "vod_play_url": "",
                }

            # 2. 只请求一次HTML详情页获取播放列表
            detail_url = HOST + "/hamigua/" + vod_id + ".html"
            html = self._http_get(detail_url, timeout=7)
            if html:
                # 补全缺失的基本信息
                if not vod.get("vod_name"):
                    m = re.search(r'<h1[^>]*>([^<]+)</h1>', html)
                    if m:
                        vod["vod_name"] = _strip(m.group(1))
                if not vod.get("vod_pic"):
                    m = re.search(r'<img[^>]+data-original="([^"]+)"[^>]*alt="[^"]*"[^>]*class="[^"]*pic[^"]*"', html)
                    if m:
                        vod["vod_pic"] = m.group(1)

                # 提取简介（优先用ajax的，如果为空则从HTML补）
                if not vod.get("vod_content"):
                    m = re.search(r'<div[^>]*class="[^"]*detail-desc-content[^"]*"[^>]*>([\s\S]*?)</div>', html)
                    if m:
                        txt = re.sub(r"<[^>]+>", " ", m.group(1)).strip()
                        if txt:
                            vod["vod_content"] = txt[:500]

                # 提取播放列表（按sid分组，不再请求播放页）
                play_from, play_url = self._collect_playlist(html, vod_id)
                if play_from:
                    vod["vod_play_from"] = "$$$".join(play_from)
                    vod["vod_play_url"] = "$$$".join(play_url)

            payload = {"list": [vod]}
            with self._cache_lock:
                self._detail_cache[vod_id] = (now, payload)
            return payload
        except Exception as e:
            print("[哈密瓜] detailContent 异常: " + str(e))
            return {"list": []}

    def _collect_playlist(self, html, vod_id):
        """从详情页HTML提取播放列表，按sid分组，不请求播放页"""
        sid_groups = {}
        for m in re.finditer(r'href="(/hamiguaplay/(\d+)-(\d+)-(\d+)\.html)"[^>]*>([^<]+)</a>', html):
            path, vid, sid, nid, name = m.groups()
            sid = int(sid)
            if sid not in sid_groups:
                sid_groups[sid] = []
            sid_groups[sid].append((int(nid), _strip(name) or "正片", path))

        if not sid_groups:
            return [], []

        play_from = []
        play_url = []

        for sid in sorted(sid_groups.keys()):
            eps = sorted(sid_groups[sid], key=lambda x: x[0])
            eps_str = [name + "$" + path for _, name, path in eps]
            if eps_str:
                # 优先从缓存取线路名，没有则用默认
                cache_key = str(vod_id) + "_" + str(sid)
                line_name = ""
                with self._cache_lock:
                    line_name = self._source_name_cache.get(cache_key, "")
                if not line_name:
                    line_name = "线路" + str(sid)
                play_from.append(line_name)
                play_url.append("#".join(eps_str))

        return play_from, play_url

    def searchContent(self, key, quick, pg="1"):
        try:
            page = int(pg or 1)
            if page < 1:
                page = 1
            cache_key = (key, page)
            now = time.time()
            with self._cache_lock:
                hit = self._search_cache.get(cache_key)
                if hit and now - hit[0] < SEARCH_CACHE_TTL:
                    return hit[1]

            kw = _urlencode(key)
            url = HOST + "/index.php/ajax/suggest?mid=1&wd=" + kw + "&limit=20&page=" + str(page)
            data = self._http_get_json(url, timeout=6)

            if not data or data.get("code") != 1:
                return {"list": [], "page": page, "pagecount": 1, "limit": 20, "total": 0}

            videos = []
            for item in data.get("list", []):
                vid = str(item.get("id", ""))
                if not vid:
                    continue
                videos.append({
                    "vod_id": vid,
                    "vod_name": _strip(item.get("name", "")),
                    "vod_pic": item.get("pic", ""),
                    "vod_remarks": "",
                })

            total = data.get("total", 0) or 0
            pagecount = data.get("pagecount", 1) or 1

            payload = {
                "list": videos,
                "page": page,
                "pagecount": pagecount,
                "limit": len(videos) or 20,
                "total": total,
            }
            with self._cache_lock:
                self._search_cache[cache_key] = (now, payload)
            return payload
        except Exception as e:
            print("[哈密瓜] searchContent 异常: " + str(e))
            return {"list": [], "page": 1, "pagecount": 1, "limit": 20, "total": 0}

    def playerContent(self, flag, id, vipFlags):
        play_path = str(id or "")
        if not play_path:
            return {"parse": 0, "url": ""}

        if self.isVideoFormat(play_path):
            return {"parse": 0, "url": play_path, "header": {"User-Agent": UA, "Referer": HOST + "/"}}

        if "/hamiguaplay/" in play_path:
            if play_path.startswith("http"):
                play_url = play_path
            else:
                play_url = HOST + play_path

            html = self._http_get(play_url, timeout=8)
            if not html:
                return {"parse": 1, "url": play_url, "header": {"User-Agent": UA, "Referer": HOST + "/"}}

            m = self._RE_PLAYER_JSON.search(html)
            if not m:
                m = self._RE_PLAYER_JSON2.search(html)
            if m:
                try:
                    player = json.loads(m.group(1))
                    real_url = player.get("url", "")
                    from_name = player.get("from", "")
                    # 缓存线路名，供详情页下次使用
                    if from_name:
                        try:
                            parts = play_path.strip("/").split("/")[-1].replace(".html", "").split("-")
                            if len(parts) >= 3:
                                vid = parts[0]
                                sid = parts[1]
                                cache_key = vid + "_" + sid
                                with self._cache_lock:
                                    self._source_name_cache[cache_key] = from_name
                        except Exception:
                            pass
                    if real_url and real_url.startswith("http"):
                        return {
                            "parse": 0,
                            "url": real_url,
                            "header": {
                                "User-Agent": UA,
                                "Referer": HOST + "/",
                            },
                        }
                except Exception as e:
                    print("[哈密瓜] player_aaaa 解析异常: " + str(e))

            return {
                "parse": 1,
                "url": play_url,
                "header": {
                    "User-Agent": UA,
                    "Referer": HOST + "/",
                }
            }

        return {"parse": 0, "url": play_path, "header": {"User-Agent": UA, "Referer": HOST + "/"}}

    def localProxy(self, param):
        return [200, "video/MP2T", b"", ""]
