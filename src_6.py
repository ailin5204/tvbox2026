# -*- coding: utf-8 -*-
# ============================================================
# DJ多多 - FongMi 影视壳 Python 源（仅兼容 FongMi，不兼容 TVBox/OK）
#
# 接口实测结论（2026-10-12）：
#   * 分类列表 https://api.djduoduo.com/category.php?cid={100..117,new,hot}
#       每类固定 20 首，无分页，内容稳定；列表内嵌 AAC 播放直链
#   * 榜单列表 https://www.djduoduo.com/share/index.php?playsrc={share,hot,new}
#       分享榜/热歌榜/新歌榜，各 20 首
#   * 单曲详情 https://www.djduoduo.com/share/get.php?act=convert&id={songid}
#       JSON: {ret, Name, Url, Cover, User}，Url/Cover 为 txcdn 直链
#   * 播放：txcdn.dianyinduoduo.com 音频直链（HTTP 206 audio/aac，FongMi parse=0 直连）
#   * 搜索：Web 端无搜索入口；App 内 v2/search.php 为 AES 加密接口，
#       密钥在爱加密壳内（dex 全量加密），静态无法获取，需真机抓包逆向。
#       当前 searchContent 返回空列表，待抓包数据补齐后在此实现。
# ============================================================

import json
import re

import requests

try:
    from base.spider import Spider as _BaseSpider
except ImportError:
    _BaseSpider = object


class Spider(_BaseSpider):
    _instance = None
    _inited = False
    DEBUG = True

    # ---------------- 接口基址 ----------------
    API_CATEGORY = "https://api.djduoduo.com/category.php"      # 官网分类
    SHARE_INDEX = "https://www.djduoduo.com/share/index.php"    # 分享/榜单页
    GET_PHP = "https://www.djduoduo.com/share/get.php"          # 详情接口

    # ---------------- 分类映射 ----------------
    # cid=100..117 为官网真实分类（各 20 首，无分页）；
    # new/hot 为虚拟分类；rank:share/rank:hot/rank:new 为分享页榜单。
    # 分类名按实测内容采样推断，可自行调整。
    TYPE_MAP = {
        "100":  "环绕音效",
        "101":  "Funky串烧",
        "102":  "网络热歌",
        "103":  "伤感情歌",
        "104":  "车载大碟",
        "105":  "中文R&B",
        "106":  "劲爆DJ",
        "107":  "流行歌曲",
        "108":  "经典老歌",
        "109":  "铃声DJ",
        "110":  "外文DJ",
        "111":  "夜店嗨曲",
        "112":  "经典串烧",
        "113":  "儿歌",
        "114":  "粤语歌曲",
        "115":  "伤感女声",
        "116":  "抖音热歌",
        "117":  "山歌民歌",
        "new":  "新上歌曲",
        "hot":  "热门歌曲",
        "rank:share": "分享榜",
        "rank:hot":   "热歌榜",
        "rank:new":   "新歌榜",
    }

    RANK_MAP = {"rank:share": "share", "rank:hot": "hot", "rank:new": "new"}

    # 分类/榜单列表页无封面图，用官网 logo 作占位（详情页返回真实封面）
    PLACEHOLDER_PIC = "https://api.djduoduo.com/img/logo.png"

    UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36"

    # ---------------- 单例与初始化 ----------------
    def __new__(cls, *args, **kwargs):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def init(self, extend=""):
        if self._inited:
            return
        self._inited = True
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": self.UA,
            "Referer": "https://www.djduoduo.com/",
        })
        self._home_cache = None
        self._detail_cache = {}

    def destroy(self):
        if self._inited:
            try:
                self.session.close()
            except Exception:
                pass
            self._inited = False

    def getName(self):
        return "DJ多多"

    # ---------------- 工具方法 ----------------
    def _log(self, msg):
        if self.DEBUG:
            print("[DJ多多]", msg)

    def _get(self, url, params=None):
        try:
            resp = self.session.get(url, params=params, timeout=10)
            resp.raise_for_status()
            return resp.text
        except Exception as e:
            self._log("请求失败 %s %s -> %s" % (url, params, e))
            return ""

    def _full_url(self, u):
        """协议相对 URL 补全 https:"""
        if not u:
            return ""
        if u.startswith("//"):
            return "https:" + u
        return u

    _LI_ITER = re.compile(r"<li\b([^>]*)>(.*?)</li>", re.S)
    _NAME_RE = re.compile(r'class="listTex2"[^>]*>(.*?)</a>', re.S)
    _PLAY_RE = re.compile(r'jPlaySong\("([^"]+)",\s*"(\d+)",\s*"play"\)')
    _TIME_RE = re.compile(r'class="listTime"[^>]*>(.*?)</span>', re.S)
    _MEN_RE = re.compile(r'class="listMen"[^>]*>(.*?)</span>', re.S)

    def _strip_tag(self, s):
        return re.sub(r"<[^>]+>", "", s or "").strip()

    _RANK_ID_RE = re.compile(r"location\.href='[^']*id=(\d+)'")
    _RANK_NAME_RE = re.compile(r'class="playTex"[^>]*>(.*?)</p>', re.S)
    _RANK_ARTIST_RE = re.compile(r'class="artist"[^>]*>(.*?)</p>', re.S)

    def _parse_category_html(self, html):
        """解析官网分类列表页：listTex2 歌名 + jPlaySong 直链 + listTime/listMen"""
        items = []
        for _attrs, block in self._LI_ITER.findall(html or ""):
            name_m = self._NAME_RE.search(block)
            play_m = self._PLAY_RE.search(block)
            if not name_m or not play_m:
                continue
            url = self._full_url(play_m.group(1))
            time_t = self._TIME_RE.search(block)
            men_t = self._MEN_RE.search(block)
            items.append({
                "songid": play_m.group(2),
                "name": self._strip_tag(name_m.group(1)),
                "url": url,
                "time": self._strip_tag(time_t.group(1)) if time_t else "",
                "men": self._strip_tag(men_t.group(1)) if men_t else "",
            })
        return items

    def _parse_rank_html(self, html, playsrc=None):
        """解析分享页榜单：li 的 onclick 自带 playsrc + id，playTex 歌名 + artist 作者（无直链）。

        关键点：share/index.php 的 playsrc 参数只用于前端 tab 切换，服务端对
        share/hot/new 三个榜单一次性全部渲染（plShare/plHot/plNew 三个 <ul>），
        请求参数怎么传都返回同一份 60 首 HTML。因此必须按每个 <li> onclick 里的
        playsrc 过滤，只取目标榜单的 20 首，否则三个分类会显示完全相同的内容。
        """
        items = []
        for attrs, block in self._LI_ITER.findall(html or ""):
            # 该 <li> 属于哪个榜单（onclick 形如 location.href='index.php?playsrc=share&id=1731534'）
            ps_m = re.search(r"playsrc=(\w+)", attrs or "")
            if playsrc and ps_m and ps_m.group(1) != playsrc:
                continue
            id_m = re.search(r"id=(\d+)", attrs or "")
            name_m = self._RANK_NAME_RE.search(block)
            artist_m = self._RANK_ARTIST_RE.search(block)
            if not id_m or not name_m:
                continue
            items.append({
                "songid": id_m.group(1),
                "name": self._strip_tag(name_m.group(1)),
                "url": "",
                "artist": self._strip_tag(artist_m.group(1)) if artist_m else "",
                "time": "",
                "men": "",
            })
        return items

    def _fetch_category(self, cid):
        """官网分类：cid=100..117 / new / hot"""
        html = self._get(self.API_CATEGORY, {"cid": cid})
        return self._parse_category_html(html)

    def _fetch_rank(self, playsrc):
        """分享页榜单：share / hot / new。

        页面一次性渲染三个榜单（各 20 首），playsrc 只管前端 tab 切换、服务端不区分；
        这里把 playsrc 透传给 _parse_rank_html，由其按 li onclick 中的 playsrc 过滤出对应榜单。
        """
        html = self._get(self.SHARE_INDEX, {"playsrc": playsrc})
        return self._parse_rank_html(html, playsrc)

    def _fetch_detail(self, songid):
        """单曲详情：get.php?act=convert&id={songid}（带缓存）"""
        if songid in self._detail_cache:
            return self._detail_cache[songid]
        text = self._get(self.GET_PHP, {"act": "convert", "id": songid})
        if not text:
            return {}
        try:
            data = json.loads(text)
        except Exception:
            return {}
        if data.get("ret") != 200:
            return {}
        name = re.sub(r"[\x00-\x1f\x7f-\x9f]+", "", data.get("Name", "")).strip()
        result = {
            "name": name or ("DJ歌曲" + str(songid)),
            "url": self._full_url(data.get("Url", "")),
            "cover": self._full_url(data.get("Cover", "")),
            "user": re.sub(r"[\x00-\x1f\x7f-\x9f]+", "", data.get("User", "")).strip(),
        }
        self._detail_cache[songid] = result
        return result

    def _vod_from_item(self, item, tid="", cover=""):
        """列表项 -> FongMi 列表条目（vod_pic 优先用传入的真实封面，无则给占位）"""
        vod = {
            "vod_id": str(item["songid"]),
            "vod_name": item["name"],
            "vod_pic": cover or self.PLACEHOLDER_PIC,
            "type_name": self.TYPE_MAP.get(tid, "DJ串烧"),
        }
        rem = []
        if item.get("time"):
            rem.append(item["time"])
        if item.get("men"):
            rem.append(item["men"] + "次播放")
        if rem:
            vod["vod_remarks"] = "/".join(rem)
        return vod

    # ---------------- FongMi 标准接口 ----------------
    def homeContent(self, filter):
        if self._home_cache is not None:
            return self._home_cache
        classes = [{"type_id": tid, "type_name": name}
                   for tid, name in self.TYPE_MAP.items()]
        result = {"class": classes, "filters": {}}
        self._home_cache = result
        return result

    def homeVideoContent(self):
        # 首页推荐：取热歌榜并补真实封面
        items = self._fetch_rank("hot")
        vods = []
        for it in items:
            info = self._fetch_detail(it["songid"])
            cover = info.get("cover", "") if info else ""
            vods.append(self._vod_from_item(it, "rank:hot", cover))
        return {"list": vods}

    def categoryContent(self, tid, pg, filter, extend):
        if str(pg) != "1":
            return {"list": [], "pagecount": 1}
        if tid in self.RANK_MAP:
            items = self._fetch_rank(self.RANK_MAP[tid])
        else:
            items = self._fetch_category(str(tid))
        vods = []
        for it in items:
            info = self._fetch_detail(it["songid"])
            cover = info.get("cover", "") if info else ""
            vods.append(self._vod_from_item(it, str(tid), cover))
        return {"list": vods, "pagecount": 1}

    def detailContent(self, ids):
        # FongMi 可能传入列表或字符串；兼容处理
        if isinstance(ids, list):
            ids = ids[0] if ids else ""
        songid = str(ids).split("/")[0].split(",")[0].strip()
        if not songid or not songid.isdigit():
            return {"list": []}
        info = self._fetch_detail(songid)
        if not info:
            return {"list": []}
        vod = {
            "vod_id": songid,
            "vod_name": info["name"],
            "vod_pic": info["cover"],
            "type_name": "DJ串烧",
            "vod_content": "作者：" + (info.get("user") or "未知"),
            "vod_play_from": "DJ多多",
            "vod_play_url": "全片播放$" + info["url"],
        }
        return {"list": [vod]}

    def searchContent(self, key, quick):
        # 搜索缺口说明：
        # 官网/分享页无搜索入口；App 内 v2/search.php 为 AES 加密接口，
        # 密钥在爱加密壳内（dex 全量加密），静态无法获取，需真机抓包逆向
        # （抓 App 搜索时 v2/search.php 的请求参数 POST 原文与响应密文）。
        # 拿到抓包数据解密后，在此实现并返回 {"list": [...]}。
        return {"list": []}

    def searchContentPage(self, key, quick, pg):
        return {"list": []}

    def playerContent(self, flag, id, vipFlags):
        url = self._full_url(id)
        # txcdn 直链实测无需额外 Referer 即可 206，但 header 里补全 UA 更稳妥
        header = json.dumps({
            "User-Agent": self.UA,
            "Referer": "https://www.djduoduo.com/",
        })
        return {"parse": 0, "url": url, "header": header}

    def isVideoFormat(self, url):
        u = (url or "").lower()
        return u.endswith((".aac", ".mp3", ".m4a", ".mp4", ".m3u8", ".flv", ".ts"))

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return None


if __name__ == "__main__":
    s = Spider()
    s.init()
    print("name:", s.getName())
    h = s.homeContent(False)
    print("home classes:", len(h["class"]))
    hv = s.homeVideoContent()
    print("home videos:", len(hv["list"]), hv["list"][0] if hv["list"] else "")
    c = s.categoryContent("104", "1", False, "")
    print("category 104:", len(c["list"]), "pagecount", c.get("pagecount"))
    if c["list"]:
        print("  first:", c["list"][0])
    d = s.detailContent(c["list"][0]["vod_id"]) if c["list"] else {}
    print("detail:", json.dumps(d, ensure_ascii=False)[:500])
    if d.get("list"):
        du = d["list"][0]["vod_play_url"].split("$")[-1]
        print("player:", json.dumps(s.playerContent("DJ多多", du, ["DJ多多"]), ensure_ascii=False))
    print("search:", s.searchContent("DJ", True))