import re
import json
import base64
import time
from urllib.parse import urlencode, quote, unquote

try:
    import requests as _requests
except Exception:
    _requests = None


HOST = "https://yy.zddyr.top"
API = HOST + "/web/api"
WEB = HOST + "/web/"

LYRIC_AS_SUB = True       # 歌词转 SRT 字幕轨（走 localProxy）
PL_TRACKS = 80            # 单个歌单最多取多少首
PER_SOURCE = 20           # 搜索时每平台取多少首
MAX_SEARCH_PAGES = 6      # 搜索分页上限
LINK_TTL = 600            # 播放直链缓存秒数

SOURCES = {
    "wy":   {"name": "网易云",  "qualities": ["128k", "320k", "flac", "hires", "atmos", "master"],
             "referer": "https://music.163.com/"},
    "tx":   {"name": "QQ音乐",  "qualities": ["128k", "192k", "320k", "flac", "hires", "atmos", "atmos_plus", "master"],
             "referer": "https://y.qq.com/"},
    "kw":   {"name": "酷我",    "qualities": ["128k", "320k", "flac"],
             "referer": "https://www.kuwo.cn/"},
    "kg":   {"name": "酷狗",    "qualities": ["128k", "320k", "flac", "hires", "atmos", "master"],
             "referer": "https://www.kugou.com/"},
    "mg":   {"name": "咪咕",    "qualities": ["128k", "320k", "flac", "hires"],
             "referer": "https://music.migu.cn/"},
    "bili": {"name": "哔哩",    "qualities": ["128k", "320k"],
             "referer": "https://www.bilibili.com/"},
}
SOURCE_KEYS = ["wy", "kg", "kw", "tx", "mg", "bili"]
PL_SOURCES = ["wy", "tx", "kw", "kg", "mg"]
LYRIC_SOURCES = ["wy", "tx", "kg"]     # 只有这三个上游有词

Q_ORDER = ["master", "atmos_plus", "atmos", "hires", "flac", "320k", "192k", "128k"]
Q_LABEL = {
    "master": "臻品母带", "atmos_plus": "全景环绕+", "atmos": "全景环绕",
    "hires": "Hi-Res", "flac": "无损FLAC", "320k": "超品320K",
    "192k": "高清192K", "128k": "标准128K",
}
LINES = ["master", "hires", "flac", "320k", "128k"]


# ───────────────────────── 小工具 ─────────────────────────

def _b64u(s):
    return base64.urlsafe_b64encode(str(s or "").encode("utf-8")).decode("ascii").rstrip("=")


def _unb64u(s):
    try:
        s = str(s or "")
        return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4)).decode("utf-8", "ignore")
    except Exception:
        return ""


def _clean(s):
    return re.sub(r"\s+", " ", str(s if s is not None else "")).replace("|", "丨").replace("$", "＄").replace("#", "＃").strip()


def _track_id(song):
    src = song.get("source")
    if src == "mg":
        return song.get("songmid") or song.get("urlId") or ""
    return song.get("urlId") or song.get("songmid") or song.get("id") or ""


def _enc_ep(song):
    """载荷：src|id|name|singer[|lyricId]  (base64url, 前缀 e)"""
    tid = _clean(_track_id(song))
    lid = _clean(song.get("lyricId") or "")
    fields = [song.get("source") or "", tid, _clean(song.get("name")), _clean(song.get("singer"))]
    if lid and lid != tid:
        fields.append(lid)
    return "e" + _b64u("|".join(fields))


def _dec_ep(s):
    s = str(s or "")
    if s.startswith("e"):
        s = s[1:]
    parts = _unb64u(s).split("|")
    tid = parts[1] if len(parts) > 1 else ""
    return {
        "source": parts[0] if parts else "",
        "id": tid,
        "name": parts[2] if len(parts) > 2 else "",
        "singer": parts[3] if len(parts) > 3 else "",
        "lyricId": (parts[4] if len(parts) > 4 and parts[4] else tid),
    }


def _norm(s):
    return re.sub(r"[\s\-_·、,，.。'’“”&/\\+~*！!？?:：]",
                  "",
                  re.sub(r"[\(\)\[\]\{\}【】（）『』「」<>《》]", "", str(s or "").lower()))


def _singer_tokens(s):
    parts = re.split(r"\s*[/、,，&＋+]\s*|\s+feat\.?\s+|\s+ft\.?\s+|\s*-\s*", str(s or "").lower())
    out = []
    for p in parts:
        n = _norm(p)
        if n and n not in out:
            out.append(n)
    return out


def _singer_match(a, b):
    A, B = _singer_tokens(a), _singer_tokens(b)
    if not A or not B:
        return True
    for x in A:
        if x in B:
            return True
    return _norm(a) == _norm(b)


def _song_key(song):
    return _norm(song.get("name")) + "@" + _norm(song.get("singer"))


NOISE_RE = re.compile(r"(live|翻唱|cover|伴奏|演奏|纯音乐|现场|演唱会|demo|片段|铃声|彩铃|加速|慢速|dj|remix|完整版|inst\b|instrumental|女声|男声|钢琴|古筝|吉他|二胡|升key|降key|原唱)", re.I)


def _decode_wd(wd):
    s = str(wd or "").strip()
    if re.search(r"%[0-9A-Fa-f]{2}", s):
        try:
            d = unquote(s).strip()
            if d and not re.search(r"%[0-9A-Fa-f]{2}", d):
                s = d
        except Exception:
            pass
    return s


def _cover_ratio(kw, text):
    k = _norm(kw)
    seen = {}
    chars = []
    for c in k:
        if not re.match(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uac00-\ud7afa-z0-9]", c):
            continue
        if c not in seen:
            seen[c] = 1
            chars.append(c)
    if not chars:
        return 1.0
    t = _norm(text)
    hit = sum(1 for c in chars if c in t)
    return hit / len(chars)


def _rel_score(name, singer, kw):
    nn, ns, nk = _norm(name), _norm(singer), _norm(kw)
    s = 0
    for raw in re.split(r"[\s　·、,，+＋&/-]+", str(kw)):
        p = _norm(raw)
        if len(p) < 2:
            continue
        if p in nn:
            s += 20
        if p in ns:
            s += 30
    s += _cover_ratio(kw, str(name) + " " + str(singer)) * 10
    if nk and nn == nk:
        s += 15
    if NOISE_RE.search(str(name) + " " + str(singer)):
        s -= 25
    return s


def _group_stats(songs, kw):
    nk = _norm(kw)
    toks = []
    for raw in re.split(r"[\s　·、,，+＋&/-]+", str(kw)):
        p = _norm(raw)
        if len(p) >= 2:
            toks.append(p)
    best_score = -1e9
    cov = 0.0
    best_tok = 0.0
    for s in songs:
        nn, ns = _norm(s.get("name")), _norm(s.get("singer"))
        sc = _rel_score(s.get("name"), s.get("singer"), kw)
        if sc > best_score:
            best_score = sc
        cv = _cover_ratio(kw, str(s.get("name")) + " " + str(s.get("singer")))
        if cv > cov:
            cov = cv
        if toks:
            hit = sum(1 for p in toks if p in nn or p in ns)
            frac = hit / len(toks)
            if frac > best_tok:
                best_tok = frac
    best_score += min(len(songs), 4) * 3
    all_tok = (not toks) or best_tok >= 0.999
    keep = (not nk) or len(nk) <= 1 or all_tok or cov >= 0.66
    return best_score, keep


def _map_quality(target, avail):
    if target in avail:
        return target
    i = Q_ORDER.index(target) if target in Q_ORDER else Q_ORDER.index("flac")
    for q in Q_ORDER[i:]:
        if q in avail:
            return q
    return avail[-1] if avail else "128k"


def _quality_ladder(target, avail):
    start = _map_quality(target, avail)
    i = Q_ORDER.index(start) if start in Q_ORDER else Q_ORDER.index("flac")
    out = [q for q in Q_ORDER[i:] if q in avail]
    return out or [start]


def _https_up(u):
    s = str(u or "")
    return "https://" + s[7:] if s.startswith("http://") else s


def _name_singer(name, singer):
    nm = _clean(name) or "未知歌曲"
    sg = _clean(singer)
    if not sg:
        return nm
    if _norm(sg) in _norm(nm):
        return nm
    return nm + " - " + sg


# ─────────────────────── 歌词：LRC → SRT ───────────────────────

def _tag_time(tag):
    m = re.match(r"^\[(\d{1,7}),(\d{1,5})\]$", tag)
    if m:
        return int(m.group(1)) / 1000.0
    m = re.match(r"^\[(\d{1,3}):(\d{1,2})(?:[.:,](\d{1,3}))?\]$", tag)
    if not m:
        return None
    sec = int(m.group(1)) * 60 + int(m.group(2))
    if m.group(3) is not None:
        sec += float("0." + m.group(3))
    return sec


def _parse_lyric(raw):
    lines = str(raw or "").replace("\r", "").split("\n")
    cues = []
    offset = 0.0
    seq = 0
    for ln in lines:
        ln = ln.lstrip("\ufeff").strip()
        if not ln:
            continue
        if ln[0] in "{}":
            continue
        om = re.search(r"\[offset:(-?\d+)\]", ln, re.I)
        if om:
            offset = int(om.group(1)) / 1000.0
            continue
        tags = re.findall(r"\[[^\]]*\]", ln)
        body = re.sub(r"<[^>]*>", "", re.sub(r"\[[^\]]*\]", "", ln)).strip()
        if not body:
            continue
        for tg in tags:
            t = _tag_time(tg)
            if t is None:
                continue
            cues.append({"t": t, "text": body, "i": seq})
            seq += 1
    for c in cues:
        c["t"] += offset
        if c["t"] < 0:
            c["t"] = 0
    cues.sort(key=lambda x: (x["t"], x["i"]))
    out = []
    for c in cues:
        if out and c["t"] == out[-1]["t"] and c["text"] == out[-1]["text"]:
            continue
        out.append(c)
    return out


def _stamp(s):
    if s < 0:
        s = 0
    h = int(s // 3600)
    mi = int((s % 3600) // 60)
    ss = int(s % 60)
    ms = int(round((s - int(s)) * 1000))
    if ms >= 1000:
        ss += 1
        ms -= 1000
    return "%02d:%02d:%02d,%03d" % (h, mi, ss, ms)


def _lrc_to_srt(lrc):
    cues = _parse_lyric(lrc)
    if not cues:
        return ""
    out = []
    for i, c in enumerate(cues):
        st = c["t"]
        en = cues[i + 1]["t"] if i + 1 < len(cues) else st + 5
        if en <= st:
            en = st + 2
        if en - st > 600:
            en = st + 600
        out.append("%d\n%s --> %s\n%s\n" % (i + 1, _stamp(st), _stamp(en), c["text"]))
    return "\n".join(out)


# ───────────────────────────── Spider ─────────────────────────────

class Spider:
    def __init__(self):
        self.site = HOST
        self.name = "星海音乐"
        self.header = {
            "User-Agent": "Mozilla/5.0 (Linux; Android 13; SM-S9080) AppleWebKit/537.36 "
                          "(KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
            "Referer": WEB,
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        }
        self.s = self.session = self.sess = _requests.Session() if _requests else None
        self.ua = self.header["User-Agent"]
        self._cache = {}
        self._host = HOST  # 某些壳子读这个
        self.cats = (
            [{"type_id": "rec", "type_name": "推荐歌单"}] +
            [{"type_id": "pl_" + s, "type_name": SOURCES[s]["name"] + "歌单"} for s in PL_SOURCES]
        )

    # ------------- OK影视 生命周期 -------------
    def init(self, extend=""):
        pass

    def getDependence(self):
        return []

    def manualVideoCheck(self):
        return False

    def isVideoFormat(self, url):
        if not url:
            return False
        u = str(url).lower()
        return u.endswith((".m3u8", ".mp4", ".flv", ".mkv", ".ts", ".avi", ".mp3", ".m4a", ".flac")) or "m3u8" in u

    def action(self, action):
        return {}

    def destroy(self):
        pass

    # ------------- 底层请求 -------------
    def _get(self, url, referer=None, timeout=20):
        h = dict(self.header)
        if referer:
            h["Referer"] = referer
        if self.s is not None:
            try:
                r = self.s.get(url, headers=h, timeout=timeout, allow_redirects=True)
                if r.status_code < 400:
                    return r.text
            except Exception:
                pass
        try:
            import urllib.request
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read().decode("utf-8", "ignore")
        except Exception:
            return ""

    def _post(self, url, data, timeout=25):
        body = json.dumps(data).encode("utf-8")
        h = dict(self.header)
        h["Content-Type"] = "application/json"
        if self.s is not None:
            try:
                r = self.s.post(url, data=body, headers=h, timeout=timeout)
                if r.status_code < 500:
                    return r.text
            except Exception:
                pass
        try:
            import urllib.request
            req = urllib.request.Request(url, data=body, headers=h, method="POST")
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read().decode("utf-8", "ignore")
        except Exception:
            return ""

    def _api(self, path, query=None, post=None, timeout=22):
        url = API + "/" + path
        if query:
            url += "?" + urlencode(query)
        txt = self._post(url, post or {}, timeout=timeout) if post is not None else self._get(url, timeout=timeout)
        if not txt:
            return None
        try:
            j = json.loads(txt)
        except Exception:
            return None
        if not isinstance(j, dict) or j.get("code") != 200:
            return None
        return j.get("data")

    # ------------- 搜索 -------------
    def _search_songs(self, source, wd, pg=1, count=20):
        d = self._api("search.php", {
            "source": source, "keyword": wd, "page": pg, "count": count,
        }, timeout=18)
        return d if isinstance(d, list) else []

    # ------------- 取链 -------------
    def _fetch_link(self, source, tid, quality):
        ck = "lk:%s:%s:%s" % (source, tid, quality)
        now = time.time()
        hit = self._cache.get(ck)
        if hit and hit[0] > now:
            return hit[1]
        d = self._api("play.php", {
            "source": source, "id": tid, "quality": quality, "t": int(now * 1000),
        }, timeout=25)
        if not d or not d.get("url"):
            raise Exception("no link")
        out = {"url": str(d["url"]).strip(), "quality": d.get("quality") or quality}
        self._cache[ck] = (now + LINK_TTL, out)
        return out

    def _find_on_other(self, source, name, singer):
        if not name:
            return None
        key = _norm(name)
        for alt in SOURCE_KEYS:
            if alt == source:
                continue
            try:
                songs = self._search_songs(alt, (name + " " + (singer or "")).strip(), 1, 8)
                for s in songs:
                    if _norm(s.get("name")) == key and _singer_match(s.get("singer"), singer):
                        return {"source": alt, "id": _track_id(s), "song": s}
            except Exception:
                pass
        return None

    # ------------- 歌词 -------------
    def _fetch_lyric_text(self, src, lid):
        d = self._api("lyric.php", {"source": src, "id": lid}, timeout=18)
        if not isinstance(d, dict):
            return ""
        return str(d.get("lyric") or d.get("yrc") or "")

    def _lyric_srt(self, src, lid):
        ck = "lr:%s:%s" % (src, lid)
        now = time.time()
        hit = self._cache.get(ck)
        if hit and hit[0] > now:
            return hit[1]
        srt = ""
        try:
            srt = _lrc_to_srt(self._fetch_lyric_text(src, lid))
        except Exception:
            pass
        if srt:
            self._cache[ck] = (now + 3600, srt)
        return srt

    def _resolve_lyric(self, src, lid, name, singer):
        own = ""
        try:
            own = self._fetch_lyric_text(src, lid)
        except Exception:
            own = ""
        if own.strip():
            return {"source": src, "id": lid}
        if not name:
            return None
        ck = "lb:%s:%s" % (src, lid)
        now = time.time()
        hit = self._cache.get(ck)
        if hit and hit[0] > now:
            return hit[1]
        key = _norm(name)
        best = None
        for alt in LYRIC_SOURCES:
            if alt == src:
                continue
            try:
                songs = self._search_songs(alt, (name + " " + (singer or "")).strip(), 1, 8)
            except Exception:
                continue
            for s in songs:
                if _norm(s.get("name")) != key:
                    continue
                if not _singer_match(s.get("singer"), singer):
                    continue
                lid2 = _clean(s.get("lyricId") or s.get("songmid") or s.get("urlId") or s.get("id") or "")
                if not lid2:
                    continue
                try:
                    txt = self._fetch_lyric_text(alt, lid2)
                except Exception:
                    txt = ""
                if txt.strip():
                    best = {"source": alt, "id": lid2}
                    break
            if best:
                break
        self._cache[ck] = (now + 6 * 3600, best)
        return best

    # ------------- Vod 组装 -------------
    def _song_to_vod(self, song, extra=None):
        src = SOURCES.get(song.get("source"), {}).get("name", song.get("source"))
        vod = {
            "vod_id": _enc_ep(song),
            "vod_name": _name_singer(song.get("name"), song.get("singer")),
            "vod_pic": _https_up(song.get("cover")),
            "vod_remarks": " · ".join([x for x in [_clean(song.get("singer")), song.get("interval")] if x]),
            "type_name": src,
            "vod_actor": _clean(song.get("singer")),
            "vod_year": "",
            "vod_content": "\n".join([
                "歌手：" + (_clean(song.get("singer")) or "未知"),
                "专辑：" + (_clean(song.get("albumName")) or "－"),
                "时长：" + (song.get("interval") or "－"),
                "平台：" + src,
            ]),
        }
        if extra:
            vod.update(extra)
        return vod

    def _build_play(self, episodes):
        lst = [e for e in episodes if e]
        if not lst:
            return "", ""
        froms, urls = [], []
        for q in LINES:
            froms.append(Q_LABEL[q])
            urls.append("#".join("%s$%s" % (e["title"], e["url"]) for e in lst))
        return "$$$".join(froms), "$$$".join(urls)

    # ================= OK影视 钩子 =================
    def homeContent(self, filter=None):
        try:
            data = self._api("playlist.php", post={
                "action": "hot", "source": "wy", "page": 1, "limit": 24, "cookie": "",
            }, timeout=25)
        except Exception:
            data = None
        lst = []
        if isinstance(data, list):
            for pl in data:
                lst.append(self._pl_to_vod(pl, "wy"))
        return {"class": self.cats, "list": lst}

    def homeVideoContent(self):
        return self.homeContent()

    def categoryContent(self, tid, pg=1, filter=None, extend=None):
        try:
            pg = int(pg)
        except Exception:
            pg = 1
        tid = str(tid or "")
        if tid == "rec":
            return self._hot_page("wy", pg, 24, pg, 8)
        src = tid.replace("pl_", "", 1)
        if src not in SOURCES or src not in PL_SOURCES:
            return {"page": pg, "pagecount": 1, "limit": 0, "total": 0, "list": []}
        return self._hot_page(src, pg, 30, pg, 20)

    def _hot_page(self, src, pg, limit, page_out, pagecount):
        try:
            data = self._api("playlist.php", post={
                "action": "hot", "source": src, "page": pg, "limit": limit, "cookie": "",
            }, timeout=28)
        except Exception:
            data = None
        arr = data if isinstance(data, list) else []
        lst = [self._pl_to_vod(pl, src) for pl in arr]
        if not lst:
            lst = [{"vod_id": "no_data", "vod_name": "没有数据", "vod_pic": "", "vod_remarks": ""}]
        return {"page": page_out, "pagecount": pagecount, "limit": len(lst), "total": len(lst), "list": lst}

    def _pl_to_vod(self, pl, src):
        play = pl.get("playCount") or 0
        if play > 100000000:
            cnt = "播放 %.1f亿" % (play / 1e8)
        elif play > 10000:
            cnt = "播放 %.1f万" % (play / 1e4)
        else:
            cnt = "播放 %s" % play if play else ""
        s = pl.get("source") or src
        remarks = " · ".join([x for x in [_clean(pl.get("author")), cnt] if x]) or SOURCES.get(src, {}).get("name", src)
        return {
            "vod_id": "pl:%s:%s" % (s, pl.get("id")),
            "vod_name": _clean(pl.get("name") or "歌单"),
            "vod_pic": _https_up(pl.get("cover")),
            "vod_remarks": remarks,
            "vod_content": _clean(pl.get("desc") or pl.get("name") or ""),
            "type_name": SOURCES.get(s, {}).get("name", s),
            "vod_actor": _clean(pl.get("author") or ""),
            "vod_year": "",
            "vod_play_from": "", "vod_play_url": "",
        }

    def searchContent(self, key, quick=False, pg="1"):
        try:
            pg = int(pg)
        except Exception:
            pg = 1
        if pg > MAX_SEARCH_PAGES:
            return {"page": pg, "pagecount": pg, "limit": 0, "total": 0, "list": []}
        wd = _decode_wd(key)
        if not wd:
            return {"page": pg, "pagecount": pg, "limit": 0, "total": 0, "list": []}

        keys = ["wy", "kw"] if quick else SOURCE_KEYS
        n = min(PER_SOURCE, 10) if quick else PER_SOURCE

        arrs = []
        for s in keys:
            try:
                arrs.append(self._search_songs(s, wd, pg, n))
            except Exception:
                arrs.append([])

        groups = {}
        order = []
        for i, arr in enumerate(arrs):
            for si, song in enumerate(arr):
                if not song or not song.get("name"):
                    continue
                k = _song_key(song)
                if k not in groups:
                    groups[k] = {"main": song, "songs": [], "rank": si}
                    order.append(k)
                g = groups[k]
                if si < g["rank"]:
                    g["rank"] = si
                g["songs"].append(song)
                if not g["main"].get("cover") and song.get("cover"):
                    g["main"] = song

        rows = []
        dropped = 0
        for idx, k in enumerate(order):
            g = groups[k]
            score, keep = _group_stats(g["songs"], wd)
            if not keep:
                dropped += 1
                continue
            rows.append({"g": g, "score": score, "rank": g["rank"], "i": idx})
        rows.sort(key=lambda x: (-x["score"], x["rank"], x["i"]))

        list_out = []
        for r in rows:
            g = r["g"]
            plats = [SOURCES.get(s.get("source"), {}).get("name", "") for s in g["songs"]]
            plats = [p for p in plats if p]
            main = g["main"]
            one = SOURCES.get(main.get("source"), {}).get("name", "")
            dur = _clean(main.get("interval"))
            remarks = ((("/".join(plats) if len(plats) > 1 else one)) + (" · " + dur if dur else "")) or one
            vod = self._song_to_vod(main, {"vod_remarks": remarks})
            # 把其他平台版本一并带进 id，省 detail 时再搜
            extra = []
            for s in g["songs"]:
                pid = _clean(_track_id(s))
                lid = _clean(s.get("lyricId") or "")
                extra.append("%s=%s%s" % (s.get("source"), pid, ("~" + lid) if lid and lid != pid else ""))
            vod["vod_id"] = vod["vod_id"] + "." + ",".join(extra)
            list_out.append(vod)

        raw_total = sum(len(a) for a in arrs)
        thin = raw_total < max(1, int(n * len(keys) / 2))
        pagecount = pg if (thin or not list_out) else MAX_SEARCH_PAGES
        if not list_out:
            list_out = [{"vod_id": "no_data", "vod_name": "没有数据", "vod_pic": "", "vod_remarks": ""}]
        return {"page": pg, "pagecount": pagecount, "limit": len(list_out), "total": len(list_out), "list": list_out}

    def detailContent(self, ids):
        vid = ids[0] if isinstance(ids, (list, tuple)) and ids else str(ids or "")
        vid = str(vid).strip()
        if not vid:
            return {"list": []}
        try:
            if vid.startswith("pl:"):
                return self._playlist_detail(vid)
            return self._song_detail(vid)
        except Exception:
            return {"list": []}

    def _song_detail(self, raw):
        body = raw[1:] if raw.startswith("e") else raw
        dot = body.find(".")
        payload = body if dot < 0 else body[:dot]
        alt_str = "" if dot < 0 else body[dot + 1:]
        ep = _dec_ep("e" + payload)

        songs = []
        if alt_str:
            for seg in alt_str.split(","):
                if "=" not in seg:
                    continue
                s_src, right = seg.split("=", 1)
                bits = right.split("~")
                if s_src in SOURCES:
                    songs.append({
                        "source": s_src, "name": ep["name"], "singer": ep["singer"],
                        "urlId": bits[0], "songmid": bits[0],
                        "lyricId": bits[1] if len(bits) > 1 else "",
                    })
        if not songs:
            songs.append({
                "source": ep["source"], "urlId": ep["id"], "songmid": ep["id"],
                "lyricId": ep["lyricId"], "name": ep["name"], "singer": ep["singer"],
            })

        cnt = {}
        for s in songs:
            cnt[s["source"]] = cnt.get(s["source"], 0) + 1
        seq = {}
        episodes = []
        for s in songs:
            one = {"source": s["source"], "name": s.get("name"), "singer": s.get("singer"),
                   "urlId": s["urlId"], "songmid": s["songmid"], "lyricId": s.get("lyricId")}
            base = SOURCES.get(s["source"], {}).get("name", s["source"])
            seq[s["source"]] = seq.get(s["source"], 0) + 1
            tag = base + str(seq[s["source"]]) if cnt[s["source"]] > 1 else base
            episodes.append({
                "title": tag + " · " + (_clean(one.get("name")) or "歌曲"),
                "url": _enc_ep(one),
            })
        play_from, play_url = self._build_play(episodes)
        vod = {
            "vod_id": raw,
            "vod_name": _name_singer(ep["name"], ep["singer"]),
            "vod_pic": "",
            "vod_remarks": _clean(ep["singer"]),
            "vod_actor": _clean(ep["singer"]),
            "type_name": SOURCES.get(ep["source"], {}).get("name", ep["source"]),
            "vod_content": "歌手：" + (_clean(ep["singer"]) or "未知") + "\n线路=音质，选集=平台版本",
            "vod_play_from": play_from,
            "vod_play_url": play_url,
        }
        return {"list": [vod]}

    def _playlist_detail(self, raw):
        seg = raw.split(":")
        if len(seg) < 3:
            return {"list": []}
        src, pid = seg[1], seg[2]
        if src not in SOURCES or not pid:
            return {"list": []}
        data = self._api("playlist.php", post={
            "action": "detail", "source": src, "id": pid, "page": 1, "limit": PL_TRACKS, "cookie": "",
        }, timeout=30)
        tracks = (data.get("list") if isinstance(data, dict) else None) or []
        if not tracks:
            return {"list": []}
        episodes = []
        for i, t in enumerate(tracks):
            episodes.append({
                "title": "%d. %s - %s" % (i + 1, _clean(t.get("name")) or "未知", _clean(t.get("singer")) or "未知"),
                "url": _enc_ep(t),
            })
        play_from, play_url = self._build_play(episodes)
        d = data if isinstance(data, dict) else {}
        vod = {
            "vod_id": raw,
            "vod_name": _clean(d.get("name") or "歌单"),
            "vod_pic": _https_up(d.get("cover")),
            "vod_remarks": "共%s首 · 取前%d首" % (d.get("total") or len(tracks), len(tracks)),
            "type_name": SOURCES[src]["name"],
            "vod_actor": _clean(d.get("author") or ""),
            "vod_director": _clean(d.get("author") or ""),
            "vod_content": _clean(d.get("desc") or "") or ("歌单《%s》 · %s" % (_clean(d.get("name") or ""), SOURCES[src]["name"])),
            "vod_play_from": play_from,
            "vod_play_url": play_url,
        }
        return {"list": [vod]}

    # ================= 播放 =================
    def playerContent(self, flag, ids, vipFlags=None):
        vid = ids[0] if isinstance(ids, (list, tuple)) and ids else str(ids or "")
        vid = str(vid or "").strip()
        if not vid:
            return {"parse": 0, "jx": 0, "url": ""}
        # 有些壳子会给选集 id 前面拼上 flag$
        if "$" in vid:
            vid = vid.split("$", 1)[-1]
        ep = _dec_ep(vid.split(".", 1)[0])
        if not ep["source"] or not ep["id"]:
            return {"parse": 0, "jx": 0, "url": "", "msg": "选集参数解析失败"}

        target = "master"
        for q in LINES:
            if Q_LABEL[q] == flag:
                target = q
                break

        link = None
        chain = {"source": ep["source"], "id": ep["id"], "lyricId": ep["lyricId"] or ep["id"]}
        avail = SOURCES.get(chain["source"], {}).get("qualities") or ["128k", "320k"]
        err = ""
        for q in _quality_ladder(target, avail):
            try:
                link = self._fetch_link(chain["source"], chain["id"], q)
                if link and link.get("url"):
                    break
            except Exception as e:
                link = None
                err = str(e)

        if not link and ep["name"]:
            alt = self._find_on_other(ep["source"], ep["name"], ep["singer"])
            if alt:
                aavail = SOURCES.get(alt["source"], {}).get("qualities") or ["128k", "320k"]
                for q in _quality_ladder(target, aavail):
                    try:
                        link = self._fetch_link(alt["source"], alt["id"], q)
                        if link and link.get("url"):
                            chain = {"source": alt["source"], "id": alt["id"],
                                     "lyricId": (alt["song"] or {}).get("lyricId") or alt["id"]}
                            break
                    except Exception as e:
                        link = None
                        err = str(e)

        if not link or not link.get("url"):
            return {"parse": 0, "jx": 0, "url": "", "msg": "取链失败：" + (err or "无可用链接")}

        notes = []
        if link.get("quality") != target:
            notes.append("该平台无%s，已退至%s" % (Q_LABEL.get(target, target), Q_LABEL.get(link.get("quality"), link.get("quality"))))
        if chain["source"] != ep["source"]:
            notes.append("原平台无可用链接，已切" + SOURCES.get(chain["source"], {}).get("name", chain["source"]))

        src = SOURCES.get(chain["source"], {})
        out = {
            "parse": 0, "jx": 0,
            "url": link["url"],
            "header": {"User-Agent": self.ua, "Referer": src.get("referer") or WEB},
            "msg": "；".join(notes),
        }

        if LYRIC_AS_SUB:
            try:
                ly = self._resolve_lyric(chain["source"], chain["lyricId"], ep["name"], ep["singer"])
                if ly:
                    if ly["source"] != chain["source"]:
                        out["msg"] = (out["msg"] + "；" if out["msg"] else "") + \
                                     "本平台无词，歌词借用" + SOURCES.get(ly["source"], {}).get("name", ly["source"]) + "同曲版本"
                    # 交给 localProxy 吐 SRT；OK影视 里通过 subs 字段挂字幕
                    sub_url = HOST + "/web/api/__pyproxy__?" + urlencode({
                        "do": "lrc", "s": ly["source"], "i": ly["id"],
                    })
                    out["subs"] = [{"name": "歌词", "url": sub_url, "lang": "cn", "format": "srt"}]
                else:
                    out["msg"] = (out["msg"] + "；" if out["msg"] else "") + "各平台都没匹配到这首歌的歌词"
            except Exception:
                pass
        return out

    # ================= 歌词代理 =================
    def localProxy(self, param):
        if not isinstance(param, dict):
            param = {}
        if param.get("do") != "lrc":
            return [404, "text/plain", b"Not Found", None]
        src = param.get("s") or ""
        lid = param.get("i") or ""
        if src not in SOURCES or not lid:
            return [404, "text/plain", b"Bad params", None]
        try:
            srt = self._lyric_srt(src, lid)
            if not srt:
                return [404, "text/plain", b"No lyric", None]
            return [200, "text/plain; charset=utf-8", srt.encode("utf-8"),
                    {"Cache-Control": "max-age=86400"}]
        except Exception:
            return [500, "text/plain", b"Error", None]