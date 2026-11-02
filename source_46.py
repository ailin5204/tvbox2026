"""
遇事不决，可问春风，春风不语，即随本心，本心坚定，何须春风！春风自有春风愁，可找鸟叔解君忧！
"""
#coding=utf-8
#!/usr/bin/python
import sys
sys.path.append('..') 
from base.spider import Spider
import re
from urllib.request import quote
import requests
class Spider(Spider):  # 元类 默认的元类 type
	hostUrl=''
	def getName(self):
		return "名称"
	def init(self,extend=""):
		print("============{0}============".format(extend))
		pass
	def isVideoFormat(self,url):
		pass
	def manualVideoCheck(self):
		pass
	def homeContent(self,filter):
		result = {}
		cateManual = {
			"鸟叔提示：这是一个搜索源，没有分类": "提示"
		}
		classes = []
		for k in cateManual:
			classes.append({
				'type_name': k,
				'type_id': cateManual[k]
			})

		result['class'] = classes
		if (filter):
			result['filters'] = self.config['filter']
		return result
	def homeVideoContent(self):
		result = {
			'list':[]
		}
		return result
	def categoryContent(self,tid,pg,filter,extend):
		result = {}
		videos=[]
		pagecount=1
		limit = len(videos)
		result['list'] = videos
		result['page'] = pg
		result['pagecount'] = pagecount
		result['limit'] = limit
		result['total'] = 10000#总计
		return result
	def detailContent(self,array):
		result = {}
		temporary = array[0].split('###')
		title=temporary[0]
		pic=temporary[-1]
		vodItems=[]
		playList=[]
		vod_play_from=[]
		url=temporary[1]
		vod_content=''
		vod = {
			"vod_id":array[0],
			"vod_name":title,
			"vod_pic":pic,
			"type_name":'',
			"vod_year":"",
			"vod_area":"",
			"vod_remarks":'',
			"vod_actor":'',
			"vod_director":'',
			"vod_content":vod_content
		}
		vod['vod_play_from'] =  "$$$".join(vod_play_from)
		vod['vod_play_url'] = "$$$".join(vodItems)
		result = {
			'list':[
				vod
			]
		}
		return result
	searchpage=1
	def searchContent(self,key,quick,pg=1):
		if int(pg)==1:
			self.searchpage=1
		if int(pg)>self.searchpage:
			return {'list':[],'page':pg}
		videos=[]
		url='https://www.panpanxia.com/api/search'
		data={"kw":key,"channels":[],"conc":0,"refresh":False,"src":"all","plugins":[],"cloud_types":[]}
		jsonData=requests.post(url,json=data).json()
		data=jsonData.get('data',[])
		videos=self.custom_list(data.get('results',[]))
		result = {
			'list':videos,
			'page':pg
		}
		return result
	def playerContent(self,flag,id,vipFlags):
		result = {}
		parse=1
		result["parse"] = parse#0=直接播放、1=嗅探
		result["playUrl"] =''
		result["url"] = id
		result["header"] = ''
		return result


	config = {
		"player": {},
		"filter": {}
		}
	header = {
		'User-Agent': 'Mozilla/5.0 (Linux; U; Android 8.0.0; zh-cn; Mi Note 2 Build/OPR1.170623.032) AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/61.0.3163.128 Mobile Safari/537.36 XiaoMi/MiuiBrowser/10.1.1'
		}
	def localProxy(self,param):
		return [200, "video/MP2T", '', ""]
	#-----------------------------------------------自定义函数-----------------------------------------------
	imgList={
	'115':'https://a1.boltp.com/2026/05/19/6a0c33ad60916.png',
	'aliyun':'https://a1.boltp.com/2026/05/19/6a0c33aeac0f8.png',
	"baidu":"https://a1.boltp.com/2026/05/19/6a0c32af640fa.png",
	"quark":"https://a1.boltp.com/2026/05/19/6a0c33ad417b7.png",
	"tianyi":"https://a1.boltp.com/2026/05/19/6a0c33ae7516d.png",
	"uc":"https://a1.boltp.com/2026/05/19/6a0c32aee784c.png",
	"mobile":"https://a1.boltp.com/2026/05/19/6a0c33af8f91f.png",
	"others":"https://a1.boltp.com/2026/05/19/6a0c33af5fb86.png",
	"xunlei":"https://a1.boltp.com/2026/05/19/6a0c33aee1b3c.png",
	"123":"https://a1.boltp.com/2026/05/19/6a0c33aeaa53a.png",
	'guangya':'https://a1.boltp.com/2026/10/12/6acc506eaaa70.png'
	}
	#正则取文本
	def custom_RegexGetText(self,reg, src, group=1):
		returnTxt=""
		Regex=re.search(reg,src, re.M|re.S)
		returnTxt="" if Regex is None else Regex.group(group)
		return returnTxt
	#分类取结果
	def custom_list(self,nodes):
		allow_disks = ['quark', 'baidu', 'uc', 'aliyun', 'guangya']
		videos = []
		for vod in nodes:
			title=vod.get('title','')
			temporary=vod.get('links',None)
			if temporary==None:
				continue
			for v in temporary:
				url=v.get('url','')
				vod_remarks=v.get('disk_type','')
				if vod_remarks not in allow_disks:
					continue
				password=v.get('password','')
				title=v.get('work_title',title)
				pic=self.imgList.get(vod_remarks,'https://tse1-mm.cn.bing.net/th/id/OIP-C.I9IpRAqSJWCBKJmwvb_03QHaLG?w=125&h=187&c=7&r=0&o=7&pid=1.7&rm=3')
				videos.append({
					"vod_id":f"push://{url}",
					"vod_name":self.custom_RegexGetText('^(.+?)(描述：|$)',title.replace('名称：','')),
					"vod_pic":pic,
					"vod_remarks":vod_remarks
					})
		return videos