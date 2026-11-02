# -*- coding: utf-8 -*-
"""
江苏名师空中课堂 OK影视Python脚本
网站: https://mskzkt.jse.edu.cn/cloudCourse/index/pc/
API: https://mskzkt.jse.edu.cn/baseApi
播放: 腾讯云点播 getplayinfo/v4
"""
import sys
import re
import json
import requests
from urllib.parse import quote

sys.path.append('..')
try:
    from base.spider import Spider
except ImportError:
    class Spider:
        def fetch(self, url, headers=None, **kw):
            import requests as rq
            kw.pop('timeout', None)
            r = rq.get(url, headers=headers, timeout=15, **kw)
            r.encoding = 'utf-8'
            return r


class Spider(Spider):
    # ======================== 基础配置 ========================
    def init(self, extend=""):
        self.host = "https://mskzkt.jse.edu.cn"
        self.base_api = "https://mskzkt.jse.edu.cn/baseApi"
        self.headers = {
            "User-Agent": "Mozilla/5.0 (Linux; Android 11; SM-G975F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.120 Mobile Safari/537.36",
            "Referer": self.host + "/",
            "Content-Type": "application/x-www-form-urlencoded",
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "Origin": self.host,
        }
        self.session = requests.Session()
        self.session.headers.update(self.headers)
        # 缓存基础数据
        self._grade_cache = {}
        self._subject_cache = {}
        self._version_cache = {}
        self._jzkt_category_cache = None
        self._xljk_category_cache = None
        self._play_url_cache = {}

    def getName(self):
        return "江苏名师空中课堂"

    def isVideoFormat(self, url):
        return bool(re.search(r'\.(m3u8|mp4|flv|avi|mkv|mov|ts)(\?|$)', url or "", re.I))

    def manualVideoCheck(self):
        return False

    # ======================== 网络请求 ========================
    def _post(self, path, data=None):
        """POST请求API"""
        try:
            url = self.base_api + path
            r = self.session.post(url, data=data or {}, timeout=15)
            if r.status_code == 200:
                return r.json()
        except Exception as e:
            print(f"[空中课堂] POST请求失败 {path}: {e}")
        return {"state": -1, "message": "请求失败"}

    def _get(self, url, headers=None):
        """GET请求"""
        try:
            r = self.session.get(url, headers=headers or self.headers, timeout=15)
            r.encoding = r.apparent_encoding or 'utf-8'
            return r.text if r.status_code == 200 else ""
        except Exception as e:
            print(f"[空中课堂] GET请求失败 {url}: {e}")
            return ""

    # ======================== 首页 ========================
    def homeContent(self, filter):
        # 动态获取筛选选项
        filters = self._build_filters()
        return {
            "class": [
                {"type_id": "seyk_1", "type_name": "同步课程-小学"},
                {"type_id": "seyk_2", "type_name": "同步课程-初中"},
                {"type_id": "seyk_3", "type_name": "同步课程-高中"},
                {"type_id": "jzkt", "type_name": "家长课堂"},
                {"type_id": "xljk", "type_name": "心理健康"},
            ],
            "filters": filters,
        }

    def homeVideoContent(self):
        """首页推荐：取同步课程小学的资源"""
        try:
            items = self._get_seyk_list(stage_id="1", page=1, limit=20)
            return {"list": items}
        except Exception:
            return {"list": []}

    def _build_filters(self):
        """动态构建筛选器"""
        filters = {}
        # 同步课程的三个学段
        for stage_id, stage_name in [("1", "小学"), ("2", "初中"), ("3", "高中")]:
            try:
                # 获取年级列表
                grade_list = self._get_grade_list(stage_id)
                grade_options = [{"n": "全部", "v": ""}]
                for g in grade_list:
                    grade_options.append({"n": g.get("grade_title", ""), "v": g.get("grade_id", "")})

                # 获取第一个年级的学科列表作为默认
                subject_options = [{"n": "全部", "v": ""}]
                if grade_list:
                    first_grade = grade_list[0].get("grade_id", "")
                    subject_list = self._get_subject_list(stage_id, first_grade)
                    for s in subject_list:
                        subject_options.append({"n": s.get("subject_title", ""), "v": s.get("subject_id", "")})

                filters[f"seyk_{stage_id}"] = [
                    {"key": "grade", "name": "年级", "value": grade_options},
                    {"key": "subject", "name": "学科", "value": subject_options},
                ]
            except Exception as e:
                print(f"[空中课堂] 构建{stage_name}筛选器失败: {e}")
                filters[f"seyk_{stage_id}"] = [
                    {"key": "grade", "name": "年级", "value": [{"n": "全部", "v": ""}]},
                    {"key": "subject", "name": "学科", "value": [{"n": "全部", "v": ""}]},
                ]

        # 家长课堂
        try:
            jzkt_cats = self._get_jzkt_category_list()
            jzkt_options = [{"n": "全部", "v": ""}]
            for c in jzkt_cats:
                jzkt_options.append({"n": c.get("category_title", ""), "v": c.get("category_id", "")})
            filters["jzkt"] = [{"key": "category", "name": "分类", "value": jzkt_options}]
        except Exception:
            filters["jzkt"] = [{"key": "category", "name": "分类", "value": [{"n": "全部", "v": ""}]}]

        # 心理健康
        try:
            xljk_cats = self._get_xljk_category_list()
            xljk_options = [{"n": "全部", "v": ""}]
            for c in xljk_cats:
                xljk_options.append({"n": c.get("category_title", ""), "v": c.get("category_id", "")})
            filters["xljk"] = [{"key": "category", "name": "分类", "value": xljk_options}]
        except Exception:
            filters["xljk"] = [{"key": "category", "name": "分类", "value": [{"n": "全部", "v": ""}]}]

        return filters

    # ======================== 分类 ========================
    def categoryContent(self, tid, pg, filter, extend):
        page = int(pg) if pg else 1
        tid = str(tid)
        ext = self._parse_extend(extend)
        # 合并filter和extend
        if isinstance(filter, dict):
            ext.update({k: str(v) for k, v in filter.items() if v})

        try:
            if tid.startswith("seyk_"):
                stage_id = tid.split("_")[1]
                items = self._get_seyk_list(stage_id=stage_id, page=page, limit=20, ext=ext)
                pagecount = 999
            elif tid == "jzkt":
                items = self._get_jzkt_list(page=page, limit=20, ext=ext)
                pagecount = 999
            elif tid == "xljk":
                items = self._get_xljk_list(page=page, limit=20, ext=ext)
                pagecount = 999
            else:
                items = []
                pagecount = 1

            return {
                "page": page,
                "pagecount": pagecount,
                "limit": 20,
                "total": len(items) * pagecount if items else 0,
                "list": items,
            }
        except Exception as e:
            print(f"[空中课堂] 分类内容异常: {e}")
            return {"page": page, "pagecount": 1, "limit": 20, "total": 0, "list": []}

    # ======================== 同步学习资源 ========================
    def _get_grade_list(self, stage_id):
        """获取年级列表（带缓存）"""
        if stage_id not in self._grade_cache:
            data = self._post("/seyk/grade/list/", {"stage_id": stage_id})
            if data.get("state") == 0:
                self._grade_cache[stage_id] = data["data"].get("grade_list", [])
            else:
                self._grade_cache[stage_id] = []
        return self._grade_cache[stage_id]

    def _get_subject_list(self, stage_id, grade_id):
        """获取学科列表（带缓存）"""
        key = f"{stage_id}_{grade_id}"
        if key not in self._subject_cache:
            data = self._post("/seyk/subject/list/", {"stage_id": stage_id, "grade_id": grade_id})
            if data.get("state") == 0:
                self._subject_cache[key] = data["data"].get("subject_list", [])
            else:
                self._subject_cache[key] = []
        return self._subject_cache[key]

    def _get_version_list(self, subject_id, grade_id):
        """获取版本列表（带缓存）"""
        key = f"{subject_id}_{grade_id}"
        if key not in self._version_cache:
            data = self._post("/seyk/version/list/", {"subject_id": subject_id, "grade_id": grade_id})
            if data.get("state") == 0:
                self._version_cache[key] = data["data"].get("version_list", [])
            else:
                self._version_cache[key] = []
        return self._version_cache[key]

    def _get_seyk_list(self, stage_id, page=1, limit=20, ext=None):
        """获取同步学习资源列表"""
        ext = ext or {}
        grade_id = ext.get("grade", "")
        subject_id = ext.get("subject", "")

        # 如果没有指定年级，取第一个
        if not grade_id:
            grade_list = self._get_grade_list(stage_id)
            if grade_list:
                grade_id = grade_list[0]["grade_id"]

        # 如果没有指定学科，取第一个
        if not subject_id and grade_id:
            subject_list = self._get_subject_list(stage_id, grade_id)
            if subject_list:
                subject_id = subject_list[0]["subject_id"]

        # 获取版本
        version_id = ""
        if subject_id and grade_id:
            version_list = self._get_version_list(subject_id, grade_id)
            if version_list:
                version_id = version_list[0]["version_id"]

        # 请求资源列表
        data = self._post("/seyk/resource/list/", {
            "subject_id": subject_id,
            "version_id": version_id,
            "volumn_id": "",
            "dir_id": "",
            "page": page,
            "limit": limit,
            "grade_id": grade_id,
            "dir_level": "",
        })

        items = []
        if data.get("state") == 0:
            resource_list = data["data"].get("resource_list", [])
            for r in resource_list:
                items.append({
                    "vod_id": f"seyk_{r.get('resource_id')}",
                    "vod_name": r.get("resource_title", ""),
                    "vod_pic": self._fix_url(r.get("seal_img", "")),
                    "vod_remarks": r.get("view", ""),
                    "vod_year": "",
                })
        return items

    # ======================== 家长课堂 ========================
    def _get_jzkt_category_list(self):
        """获取家长课堂分类列表（带缓存）"""
        if self._jzkt_category_cache is None:
            data = self._post("/jzkt/category/list/", {})
            if data.get("state") == 0:
                self._jzkt_category_cache = data["data"].get("category_list", [])
            else:
                self._jzkt_category_cache = []
        return self._jzkt_category_cache

    def _get_jzkt_list(self, page=1, limit=20, ext=None):
        """获取家长课堂资源列表（修复：使用list API传category_id，而非recommend+客户端过滤）"""
        ext = ext or {}
        category_id = ext.get("category", "")

        # 使用resource/list API，支持category_id参数
        params = {"page": page, "limit": limit}
        if category_id:
            params["category_id"] = category_id
        data = self._post("/jzkt/resource/list/", params)

        items = []
        if data.get("state") == 0:
            resource_list = data["data"].get("resource_list", [])
            for r in resource_list:
                items.append({
                    "vod_id": f"jzkt_{r.get('resource_id')}",
                    "vod_name": r.get("resource_title", ""),
                    "vod_pic": self._fix_url(r.get("seal_img", "")),
                    "vod_remarks": r.get("view", ""),
                    "vod_year": "",
                })
        return items

    # ======================== 心理健康 ========================
    def _get_xljk_category_list(self):
        """获取心理健康分类列表（带缓存，只保留有内容的分类）"""
        if self._xljk_category_cache is None:
            data = self._post("/xljk/category/list/", {})
            if data.get("state") == 0:
                # 展平所有分类（包括子分类）
                all_cats = []
                for cat in data["data"].get("category_list", []):
                    all_cats.append(cat)
                    for child in cat.get("child_list", []):
                        all_cats.append(child)
                # 只保留有内容的分类（107家长·育心课堂、108教师·爱心讲堂、109学生·知心学堂）
                valid_ids = {"107", "108", "109"}
                self._xljk_category_cache = [c for c in all_cats if str(c.get("category_id", "")) in valid_ids]
            else:
                self._xljk_category_cache = []
        return self._xljk_category_cache

    def _get_xljk_list(self, page=1, limit=20, ext=None):
        """获取心理健康资源列表"""
        ext = ext or {}
        category_id = ext.get("category", "")

        # 如果没有指定分类，合并返回所有有内容的分类
        if not category_id:
            all_items = []
            for cat in self._get_xljk_category_list():
                cid = str(cat.get("category_id", ""))
                items = self._fetch_xljk_by_category(cid, page, limit)
                all_items.extend(items)
            # 按page和limit分页
            start = (page - 1) * limit
            return all_items[start:start + limit]

        return self._fetch_xljk_by_category(category_id, page, limit)

    def _fetch_xljk_by_category(self, category_id, page=1, limit=20):
        """按分类获取心理健康资源"""
        params = {"page": page, "limit": limit, "category_id": category_id}
        data = self._post("/xljk/resource/list/", params)

        items = []
        if data.get("state") == 0:
            resource_list = data["data"].get("resource_list", [])
            for r in resource_list:
                items.append({
                    "vod_id": f"xljk_{r.get('resource_id')}",
                    "vod_name": r.get("resource_title", r.get("teacher_title", "")),
                    "vod_pic": self._fix_url(r.get("seal_img", "")),
                    "vod_remarks": r.get("view", ""),
                    "vod_year": "",
                })
        return items

    # ======================== 详情 ========================
    def detailContent(self, ids):
        vid = str(ids[0]) if isinstance(ids, list) else str(ids)
        try:
            module, resource_id = vid.split("_", 1)
        except ValueError:
            return {"list": []}

        # 根据模块调用对应的详情API
        if module == "seyk":
            data = self._post("/seyk/resource/detail/", {"resource_id": resource_id})
        elif module == "jzkt":
            data = self._post("/jzkt/resource/detail/", {"resource_id": resource_id})
        elif module == "xljk":
            data = self._post("/xljk/resource/detail/", {"resource_id": resource_id})
        else:
            return {"list": []}

        if data.get("state") != 0:
            return {"list": []}

        info = data["data"].get("resource_info", {})
        title = info.get("title", info.get("resource_title", ""))
        pic = self._fix_url(info.get("seal_img", info.get("thumb", "")))
        desc = info.get("description", info.get("article_content", ""))
        view = info.get("view", "")

        # 构造播放线路（只有一条线路）
        play_from = "默认线路"
        play_url = f"播放${vid}"

        return {
            "list": [{
                "vod_id": vid,
                "vod_name": title,
                "vod_pic": pic,
                "vod_content": self._clean(desc),
                "vod_remarks": view,
                "vod_play_from": play_from,
                "vod_play_url": play_url,
            }]
        }

    # ======================== 播放（核心修复） ========================
    def playerContent(self, flag, id, vipFlags):
        vid = str(id or "")
        try:
            module, resource_id = vid.split("_", 1)
        except ValueError:
            return {"parse": 0, "url": "", "msg": "无效的资源ID"}

        # 检查缓存
        if vid in self._play_url_cache:
            cached = self._play_url_cache[vid]
            return {"parse": 0, "url": cached, "header": self._play_headers()}

        # 1. 获取资源详情，得到file_id
        if module == "seyk":
            detail_data = self._post("/seyk/resource/detail/", {"resource_id": resource_id})
        elif module == "jzkt":
            detail_data = self._post("/jzkt/resource/detail/", {"resource_id": resource_id})
        elif module == "xljk":
            detail_data = self._post("/xljk/resource/detail/", {"resource_id": resource_id})
        else:
            return {"parse": 0, "url": "", "msg": "未知的资源类型"}

        if detail_data.get("state") != 0:
            return {"parse": 0, "url": "", "msg": "获取资源详情失败"}

        info = detail_data["data"].get("resource_info", {})
        file_id = info.get("file_id", "")
        if not file_id:
            return {"parse": 0, "url": "", "msg": "无file_id"}

        # 2. 调用/base/vod/获取app_id和psign
        vod_data = self._post("/base/vod/", {"file_id": file_id})
        if vod_data.get("state") != 0:
            return {"parse": 0, "url": "", "msg": "获取播放签名失败"}

        app_id = vod_data["data"].get("app_id", "")
        psign = vod_data["data"].get("psign", "")
        if not app_id or not psign:
            return {"parse": 0, "url": "", "msg": "无app_id或psign"}

        # 3. 调用腾讯云getplayinfo/v4 API获取带签名的m3u8播放地址
        play_url = self._get_tencent_play_url(app_id, file_id, psign)
        if not play_url:
            return {"parse": 0, "url": "", "msg": "获取播放地址失败"}

        # 缓存播放地址
        self._play_url_cache[vid] = play_url

        return {
            "parse": 0,
            "url": play_url,
            "header": self._play_headers(),
        }

    def _get_tencent_play_url(self, app_id, file_id, psign):
        """调用腾讯云getplayinfo/v4 API获取播放地址（修复：兼容新老视频返回结构，老视频videoInfo在根级别）"""
        try:
            url = f"https://playvideo.qcloud.com/getplayinfo/v4/{app_id}/{file_id}?psign={psign}"
            headers = {
                "User-Agent": self.headers["User-Agent"],
                "Referer": self.host + "/",
                "Origin": self.host,
            }
            r = requests.get(url, headers=headers, timeout=15)
            if r.status_code == 200:
                data = r.json()
                if data.get("code") == 0:
                    # 兼容两种结构：新视频有media，老视频直接在根级别
                    media = data.get("media", {}) or {}
                    streaming = media.get("streamingInfo", {}) or data.get("streamingInfo", {}) or {}
                    # 优先使用adaptiveDynamicStreamingInfo（m3u8）
                    adaptive = streaming.get("adaptiveDynamicStreamingInfo", {})
                    if adaptive and adaptive.get("url"):
                        return adaptive["url"]
                    # 其次使用plainOutput（m3u8）
                    plain = streaming.get("plainOutput", {})
                    if plain and plain.get("url"):
                        return plain["url"]
                    # 备用1：使用videoInfo.sourceVideo.url（带签名的MP4直链，老视频）
                    video_info = media.get("videoInfo", {}) or data.get("videoInfo", {}) or {}
                    source = video_info.get("sourceVideo", {})
                    if source and source.get("url"):
                        return source["url"]
                    # 备用2：使用transcodeList中的第一个地址
                    transcode_list = video_info.get("transcodeList", [])
                    if transcode_list and transcode_list[0].get("url"):
                        return transcode_list[0]["url"]
        except Exception as e:
            print(f"[空中课堂] 获取腾讯云播放地址失败: {e}")
        return ""

    def _play_headers(self):
        """播放请求的header"""
        return {
            "User-Agent": self.headers["User-Agent"],
            "Referer": self.host + "/",
            "Origin": self.host,
        }

    # ======================== 搜索 ========================
    def searchContent(self, key, quick, pg="1"):
        page = int(pg) if pg else 1
        try:
            from urllib.parse import unquote
            decoded = unquote(str(key))
        except Exception:
            decoded = str(key)

        data = self._post("/search/", {
            "keyword": decoded,
            "page": page,
            "limit": 20,
        })

        items = []
        if data.get("state") == 0:
            resource_list = data["data"].get("resource_list", [])
            # module映射: 7=同步课程(seyk), 106=家长课堂(jzkt), 3=心理健康(xljk)
            module_map = {"7": "seyk", "106": "jzkt", "3": "xljk"}
            for r in resource_list:
                res_id = r.get("res_id", "")
                module = str(r.get("module", ""))
                prefix = module_map.get(module, "seyk")
                items.append({
                    "vod_id": f"{prefix}_{res_id}",
                    "vod_name": r.get("res_title", ""),
                    "vod_pic": self._fix_url(r.get("seal_img", "")),
                    "vod_remarks": r.get("view", ""),
                    "vod_year": "",
                })

        return {
            "list": items,
            "page": page,
            "pagecount": 999,
            "limit": 20,
            "total": len(items),
        }

    # ======================== 辅助方法 ========================
    def _parse_extend(self, extend):
        """解析extend参数"""
        if not extend:
            return {}
        if isinstance(extend, dict):
            return extend
        s = str(extend).strip()
        try:
            return json.loads(s)
        except Exception:
            pass
        if '=' in s:
            d = {}
            sep = '&' if '&' in s else (';' if ';' in s else None)
            for part in (s.split(sep) if sep else [s]):
                if '=' in part:
                    k, v = part.split('=', 1)
                    d[k.strip()] = v.strip()
            if d:
                return d
        return {}

    def _fix_url(self, url):
        """修复URL"""
        if not url:
            return ""
        if url.startswith("//"):
            return "https:" + url
        if url.startswith("/"):
            return self.host + url
        return url

    def _clean(self, text):
        """清理HTML标签"""
        if not text:
            return ""
        text = re.sub(r"<[^>]+>", "", text)
        text = re.sub(r"\s+", " ", text)
        return text.strip()

    def localProxy(self, param):
        return [404, "text/plain", "", ""]

    def destroy(self):
        return "正在Destroy"