import json
import os
import shutil

from flask import Flask, request, Response, stream_with_context
from flask import send_from_directory
from core.nfo import write_nfo
from core.config import cfg, args
from core.file import *
from core.func import *
from core.image import *
from core.datatype import Movie, MovieInfo
from web.base import download
from web.translate import translate_movie_info
from core.print import TqdmOut
from core.baidu_aip import aip_crop_poster
from core.datatype import ColoredFormatter
from core.avid import *
from shutil import copyfile
from os import environ

import logging
import colorama
import threading
import requests
import sys
import time
import re

logger = logging.getLogger(__name__)
app = Flask(__name__)


def info_summary(movie: Movie, all_info):
    """汇总多个来源的在线数据生成最终数据"""
    final_info = MovieInfo(movie)
    ########## 部分字段配置了专门的选取逻辑，先处理这些字段 ##########
    # genre
    if 'javdb' in all_info:
        final_info.genre = all_info['javdb'].genre

    ########## 然后检查所有字段，如果某个字段还是默认值，则按照优先级选取数据 ##########
    # parser直接更新了all_info中的项目，而初始all_info是按照优先级生成的，已经符合配置的优先级顺序了
    # 按照优先级取出各个爬虫获取到的信息
    attrs = [i for i in dir(final_info) if not i.startswith('_')]
    covers, big_covers = [], []
    for name, data in all_info.items():
        absorbed = []
        # 遍历所有属性，如果某一属性当前值为空而爬取的数据中含有该属性，则采用爬虫的属性
        for attr in attrs:
            incoming = getattr(data, attr)
            if attr == 'cover':
                if incoming and (incoming not in covers):
                    covers.append(incoming)
                    absorbed.append(attr)
            elif attr == 'big_cover':
                if incoming and (incoming not in big_covers):
                    big_covers.append(incoming)
                    absorbed.append(attr)
            else:
                current = getattr(final_info, attr)
                if (not current) and (incoming):
                    setattr(final_info, attr, incoming)
                    absorbed.append(attr)
        if absorbed:
            logger.debug(f"从'{name}'中获取了字段: " + ' '.join(absorbed))
    # 使用网站的番号作为番号
    if cfg.Crawler.respect_site_avid:
        id_weight = {}
        for name, data in all_info.items():
            if data.title:
                if movie.dvdid:
                    id_weight.setdefault(data.dvdid, []).append(name)
                else:
                    id_weight.setdefault(data.cid, []).append(name)
        # 根据权重选择最终番号
        if id_weight:
            id_weight = {k: v for k, v in sorted(id_weight.items(), key=lambda x: len(x[1]), reverse=True)}
            final_id = list(id_weight.keys())[0]
            if movie.dvdid:
                final_info.dvdid = final_id
            else:
                final_info.cid = final_id
    setattr(final_info, 'covers', covers)
    setattr(final_info, 'big_covers', big_covers)
    # 对cover和big_cover赋值，避免后续检查必须字段时出错
    if covers:
        final_info.cover = covers[0]
    if big_covers:
        final_info.big_cover = big_covers[0]
    ########## 部分字段放在最后进行检查 ##########
    # title
    if cfg.Crawler.title__chinese_first and 'airav' in all_info:
        if all_info['airav'].title and final_info.title != all_info['airav'].title:
            final_info.ori_title = final_info.title
            final_info.title = all_info['airav'].title
    # 检查是否所有必需的字段都已经获得了值
    for attr in cfg.Crawler.required_keys:
        if not getattr(final_info, attr, None):
            logger.error(f"所有爬虫均未获取到字段: '{attr}'，抓取失败")
            return False
    # 必需字段均已获得了值：将最终的数据附加到movie
    movie.info = final_info
    return True


def info_cover(info: MovieInfo, provider: str):
    return \
        {
            "id": info.dvdid,
            "number": info.dvdid,
            "title": info.title,
            "provider": provider,
            "homepage": "",
            "thumb_url": info.cover,
            "cover_url": info.big_cover or info.cover,
            "score": info.score or '0',
            "actors": info.actress or [],
            "release_date": "0001-01-01T00:00:00Z"  # info.publish_date +
        }


def generate_names(movie: Movie):
    """按照模板生成相关文件的文件名"""
    info = movie.info
    # 准备用来填充命名模板的字典
    d = {}
    d['num'] = info.dvdid
    d['title'] = info.title or cfg.NamingRule.null_for_title
    d['rawtitle'] = info.ori_title or d['title']
    if info.actress and len(info.actress) > cfg.NamingRule.max_acctress_count:
        logging.debug('女优人数过多，按配置保留了其中的前n个: ' + ','.join(info.actress))
        actress = info.actress[:cfg.NamingRule.max_acctress_count] + ['…']
    else:
        actress = info.actress
    d['actress'] = ','.join(actress) if actress else cfg.NamingRule.null_for_actress
    d['score'] = info.score or '0'
    d['serial'] = info.serial or cfg.NamingRule.null_for_serial
    d['director'] = info.director or cfg.NamingRule.null_for_director
    d['producer'] = info.producer or cfg.NamingRule.null_for_producer
    d['publisher'] = info.publisher or cfg.NamingRule.null_for_publisher
    d['date'] = info.publish_date or '0000-00-00'
    d['year'] = d['date'].split('-')[0]
    # cid中不会出现'-'，可以直接从d['num']拆分出label
    num_items = d['num'].split('-')
    d['label'] = num_items[0] if len(num_items) > 1 else '---'
    # 保存label供后面判断裁剪图片的方式使用
    setattr(info, 'label', d['label'].upper())
    # 处理字段：替换不能作为文件名的字符，移除首尾的空字符
    for k, v in d.items():
        d[k] = replace_illegal_chars(v.strip())

    # 生成nfo文件中的影片标题
    nfo_title = cfg.NamingRule.nfo_title.substitute(**d)
    setattr(info, 'nfo_title', nfo_title)

    # 使用字典填充模板，生成相关文件的路径（多分片影片要考虑CD-x部分）
    cdx = '' if len(movie.files) <= 1 else '-CD1'
    if hasattr(info, 'title_break'):
        title_break = info.title_break
    else:
        title_break = split_by_punc(d['title'])
    if hasattr(info, 'ori_title_break'):
        ori_title_break = info.ori_title_break
    else:
        ori_title_break = split_by_punc(d['rawtitle'])
    copyd = d.copy()
    for end in range(len(ori_title_break), 0, -1):
        copyd['rawtitle'] = replace_illegal_chars(''.join(ori_title_break[:end]).strip())
        for sub_end in range(len(title_break), 0, -1):
            copyd['title'] = replace_illegal_chars(''.join(title_break[:sub_end]).strip())
            save_dir = os.path.normpath(cfg.NamingRule.save_dir.substitute(copyd)).strip()
            basename = os.path.normpath(cfg.NamingRule.filename.substitute(copyd).strip())
            fanart_file = os.path.join(save_dir, f'{basename}{cdx}-fanart.jpg')
            remaining = get_remaining_path_len(os.path.abspath(fanart_file))
            if remaining > 0:
                movie.save_dir = save_dir
                movie.basename = basename
                movie.nfo_file = os.path.join(save_dir, f'{basename}{cdx}.nfo')
                movie.fanart_file = fanart_file
                movie.poster_file = os.path.join(save_dir, f'{basename}{cdx}-poster.jpg')
                if d['title'] != copyd['title']:
                    logger.info(f"自动截短标题为:\n{copyd['title']}")
                if d['rawtitle'] != copyd['rawtitle']:
                    logger.info(f"自动截短原始标题为:\n{copyd['rawtitle']}")
                return
    else:
        # 以防万一，当整理路径非常深或者标题起始很长一段没有标点符号时，硬性截短生成的名称
        templates = cfg.NamingRule.save_dir.template + os.sep + cfg.NamingRule.filename.template
        copyd['title'] = copyd['title'][:remaining]
        copyd['rawtitle'] = copyd['rawtitle'][:remaining]
        if (copyd['title'] == '' and '$title' in templates) or (copyd['rawtitle'] == '' and '$rawtitle' in templates):
            logger.error("命名规则导致标题被截断至空，请增大'max_path_len'或减小'max_acctress_count'配置项后重试")
            logger.debug((d, templates, cfg.NamingRule.max_path_len))
            return
        save_dir = os.path.normpath(cfg.NamingRule.save_dir.substitute(copyd)).strip()
        movie.save_dir = save_dir
        movie.basename = os.path.normpath(cfg.NamingRule.filename.substitute(copyd)).strip()
        movie.nfo_file = os.path.join(save_dir, f'{basename}{cdx}.nfo')
        movie.fanart_file = os.path.join(save_dir, f'{basename}{cdx}-fanart.jpg')
        movie.poster_file = os.path.join(save_dir, f'{basename}{cdx}-poster.jpg')
        if d['title'] != copyd['title']:
            logger.info(f"自动截短标题为:\n{copyd['title']}")
        if d['rawtitle'] != copyd['rawtitle']:
            logger.info(f"自动截短原始标题为:\n{copyd['rawtitle']}")


# 爬虫是IO密集型任务，可以通过多线程提升效率
def parallel_crawler(movie):
    """使用多线程抓取不同网站的数据"""

    def wrapper(parser, info: MovieInfo, retry):
        """对抓取器函数进行包装，便于更新提示信息和自动重试"""
        crawler_name = threading.current_thread().name
        task_info = f'Crawler: {crawler_name}: {info.dvdid}'
        for cnt in range(retry):
            try:
                parser(info)
                logger.debug(f'{task_info}: 抓取成功')
                break
            except requests.exceptions.RequestException as e:
                logger.debug(f'{task_info}: 网络错误，正在重试 ({cnt + 1}/{retry}): \n{repr(e)}')
            except Exception as e:
                logger.error(e)
                logger.debug(e, exc_info=True)
                break

    # 根据影片的数据源获取对应的抓取器
    crawler_mods = cfg.CrawlerSelect[movie.data_src]
    all_info = {i: MovieInfo(movie) for i in crawler_mods}

    thread_pool = []
    for mod, info in all_info.items():
        parser = getattr(sys.modules[mod], 'parse_data')
        # 将all_info中的info实例传递给parser，parser抓取完成后，info实例的值已经完成更新
        # TODO: 抓取器如果带有parse_data_raw，说明它已经自行进行了重试处理，此时将重试次数设置为1
        if hasattr(sys.modules[mod], 'parse_data_raw'):
            th = threading.Thread(target=wrapper, name=mod, args=(parser, info, 1))
        else:
            th = threading.Thread(target=wrapper, name=mod, args=(parser, info, cfg.Network.retry))
        th.start()
        thread_pool.append(th)
    # 等待所有线程结束
    timeout = cfg.Network.retry * cfg.Network.timeout
    for th in thread_pool:
        th.join(timeout=timeout)

    # 删除all_info中键名中的'web.'
    all_info = {k[4:]: v for k, v in all_info.items()}
    return all_info


def download_cover(covers, fanart_path, big_covers=[]):
    """下载封面图片"""
    # 优先下载高清封面
    fanart_base = os.path.splitext(fanart_path)[0] + '.'
    for url in big_covers:
        pic_path = fanart_base + url.split('.')[-1].lower()
        for _ in range(cfg.Network.retry):
            try:
                info = download(url, pic_path)
                if valid_pic(pic_path):
                    filesize = get_fmt_size(pic_path)
                    width, height = get_pic_size(pic_path)
                    elapsed = time.strftime("%M:%S", time.gmtime(info['elapsed']))
                    speed = get_fmt_size(info['rate']) + '/s'
                    logger.info(f"已下载高清封面: {width}x{height}, {filesize} [{elapsed}, {speed}]")
                    return (url, pic_path)
            except requests.exceptions.HTTPError:
                # HTTPError通常说明猜测的高清封面地址实际不可用，因此不再重试
                break
    # 如果没有高清封面或高清封面下载失败
    for url in covers:
        pic_path = fanart_base + url.split('.')[-1].lower()
        for _ in range(cfg.Network.retry):
            try:
                download(url, pic_path)
                if valid_pic(pic_path):
                    logger.debug(f"已下载封面: '{url}'")
                    return (url, pic_path)
                else:
                    logger.debug(f"图片无效或已损坏: '{url}'，尝试更换下载地址")
                    break
            except Exception as e:
                logger.debug(e, exc_info=True)
    logger.error(f"下载封面图片失败")
    logger.debug('big_covers:' + str(big_covers) + ', covers' + str(covers))
    return None


def crop_poster_wrapper(fanart_file, poster_file, method='normal'):
    """包装各种海报裁剪方法，提供统一的调用"""
    if cfg.Picture.ai_engine == 'baidu':
        try:
            aip_crop_poster(fanart_file, poster_file)
        except Exception as e:
            logger.debug('人脸识别失败，回退到常规裁剪方法')
            logger.debug(e, exc_info=True)
            crop_poster(fanart_file, poster_file)
    else:
        crop_poster(fanart_file, poster_file)


def postStep_videostation(movie: Movie):
    """使用群晖Video Station时，生成额外的影片poster、fanart文件"""
    fanart_ext = os.path.splitext(movie.fanart_file)[1]
    for file in movie.new_paths:
        # 创建与影片同名的fanart
        samename_fanart = os.path.splitext(file)[0] + fanart_ext
        copyfile(movie.fanart_file, samename_fanart)
        # 将现有poster以新名字复制一份
        samename_poster = os.path.splitext(file)[0] + '.png'
        crop_poster(movie.poster_file, samename_poster)


def zip_file(path, zipfilename):
    import zipfile
    z = zipfile.ZipFile(zipfilename, 'w', zipfile.ZIP_DEFLATED)
    for dirpath, dirnames, filenames in os.walk(path):
        for filename in filenames:
            z.write(os.path.join(dirpath, filename))
    z.close()


def postStep_MultiMoviePoster(movie: Movie):
    """为多分片的影片创建额外的poster图片"""
    # Jellyfin将多分片影片视作CD1的附加部分，nfo文件名、fanart均使用的CD1的文件名，
    # 只有poster是为各个分片创建的
    for i, _ in enumerate(movie.files[1:], start=2):
        cdx_poster = os.path.join(movie.save_dir, f'{movie.basename}-CD{i}-poster.jpg')
        copyfile(movie.poster_file, cdx_poster)


def import_crawlers(cfg):
    """按配置文件的抓取器顺序将该字段转换为抓取器的函数列表"""
    unknown_mods = []
    for typ, cfg_str in cfg.CrawlerSelect.items():
        mods = cfg_str.split(',')
        if 'airav' in mods:
            mods.sort(key=lambda x: x == 'airav', reverse=cfg.Crawler.title__chinese_first)
        valid_mods = []
        for name in mods:
            try:
                # 导入fc2fan抓取器的前提: 配置了fc2fan的本地路径
                if name == 'fc2fan' and (not os.path.isdir(cfg.Crawler.fc2fan_local_path)):
                    logger.debug('由于未配置有效的fc2fan路径，已跳过该抓取器')
                    continue
                import_name = 'web.' + name
                __import__(import_name)
                valid_mods.append(import_name)  # 抓取器有效: 使用完整模块路径，便于程序实际使用
            except ModuleNotFoundError:
                unknown_mods.append(name)  # 抓取器无效: 仅使用模块名，便于显示
        cfg._sections['CrawlerSelect'][typ] = tuple(valid_mods)
    if unknown_mods:
        logger.warning('配置的抓取器无效: ' + ', '.join(unknown_mods))


@app.route('/')
def hello_word():
    return 'Hello Jav'


@app.route('/images/<dvdid>/<web>/<file>', methods=['GET', 'POST'])
def send_images(dvdid, web, file):
    return send_from_directory(os.path.join(cfg.NamingRule.output_folder, dvdid, web), file)


@app.route('/v1/images/primary/<provider>/<dvdid>', methods=['GET', 'POST'])
def show_images(provider, dvdid):
    url = request.args.get('url')
    req = requests.get(url, stream=True)
    return Response(stream_with_context(req.iter_content(2048)), content_type=req.headers['content-type'])


@app.route('/v1/movies/<provider>/<dvdid>', methods=['GET', 'POST'])
def get_movies_info(provider, dvdid):
    try:
        info = MovieInfo(from_file=os.path.join(cfg.NamingRule.output_folder, dvdid, f'{provider}.json'))
        return json.dumps({"data": {
            "id": info.dvdid,
            "number": info.dvdid,
            "title": info.title,
            "summary": info.plot or "",
            "provider": provider,
            "homepage": info.url or "",
            "director": info.director or "",
            "actors": info.actress or "",
            "thumb_url": "",
            "big_thumb_url": "",
            "cover_url": info.cover,
            "big_cover_url": info.big_cover or "",
            "preview_video_url": info.preview_video or "",
            "preview_video_hls_url": "",
            "preview_images": info.preview_pics or [],
            "maker": info.publisher or "",
            "label": "",
            "series": info.serial or "",
            "genres": info.genre or [],
            "score": info.score or 0,
            "runtime": info.duration or 0,
            "release_date": "0001-01-01T00:00:00Z"
        }})
    except:
        return ""


@app.route('/v1/movies/search', methods=['GET', 'POST'])
def search_movies():
    def check_step(result, msg='步骤错误'):
        """检查一个整理步骤的结果，并负责更新tqdm的进度"""
        if not result:
            raise Exception(msg)

    try:
        fullpath = request.args.get('q')
        dvdid = get_id(fullpath)
        logging.info(f"从文件{fullpath}中解析出{dvdid}")

        movie = Movie(dvdid)

        all_info = parallel_crawler(movie)

        movie.save_dir = cfg.NamingRule.output_folder
        # if not os.path.exists(movie.save_dir):
        #    os.makedirs(movie.save_dir)
        '''
        for k, v in all_info.items():
            if v.cover is not None:
                cover_dl = download_cover([v.cover], os.path.join(movie.save_dir, v.dvdid, k, "cover.jpg"))
                if cover_dl:
                    _, cover = cover_dl
                    v.cover = (request.host_url + "images" + cover[len(movie.save_dir):]).replace('\\', '/')
        '''
        logger.info('汇总数据')
        has_required_keys = info_summary(movie, all_info)
        check_step(has_required_keys, '抓取电影内容失败')

        # all_infos = {"summary": movie.info}
        # all_infos.update()

        # generate_names_for_download(movie)

        movies_info = {"data": []}
        movie.info.dump(os.path.join(movie.save_dir, movie.info.dvdid, f'summary.json'))
        movies_info["data"].append(info_cover(movie.info, "summary"))
        for key, value in all_info.items():
            value.dump(os.path.join(movie.save_dir, value.dvdid, f'{key}.json'))
            if value.title is not None and value.cover is not None:
                movies_info["data"].append(info_cover(value, key))

        return json.dumps(movies_info)
    except:
        return ""


'''
        generate_names(movie)
        check_step(movie.save_dir, '无法按命名规则生成目标文件夹')

        logger.info('下载封面图片')
        if not os.path.exists(movie.save_dir):
            os.makedirs(movie.save_dir)

        if cfg.Picture.use_big_cover:
            cover_dl = download_cover(movie.info.covers, movie.fanart_file, movie.info.big_covers)
        else:
            cover_dl = download_cover(movie.info.covers, movie.fanart_file)
        check_step(cover_dl, '下载封面图片失败')
        cover, pic_path = cover_dl
        # 确保实际下载的封面的url与即将写入到movie.info中的一致
        if cover != movie.info.cover:
            movie.info.cover = cover
        # 根据实际下载的封面的格式更新fanart/poster等图片的文件名
        if pic_path != movie.fanart_file:
            movie.fanart_file = pic_path
            actual_ext = os.path.splitext(pic_path)[1]
            movie.poster_file = os.path.splitext(movie.poster_file)[0] + actual_ext

        if cfg.Picture.use_ai_crop and (
                movie.info.uncensored or
                movie.data_src == 'fc2' or
                movie.info.label.upper() in cfg.Picture.use_ai_crop_labels or
                (R'\d' in cfg.Picture.use_ai_crop_labels and re.match(r'(\d{6}[-_]\d{3})', movie.info.dvdid))):
            method = cfg.Picture.ai_engine
            logger.info('使用AI裁剪海报封面')
        else:
            logger.info('裁剪海报封面')
            method = 'normal'
        crop_poster_wrapper(movie.fanart_file, movie.poster_file, method)

        if 'video_station' in cfg.NamingRule.media_servers:
            postStep_videostation(movie)
        if len(movie.files) > 1:
            postStep_MultiMoviePoster(movie)

        logger.info('写入NFO')
        write_nfo(movie.info, movie.nfo_file)

        for key, value in all_info.items():
            value.dump(os.path.join(movie.save_dir, f'{dvdid}_{key}.json'))
        movie.info.dump(os.path.join(movie.save_dir, f'{dvdid}.json'))

        logger.info('移动影片文件')
        movie.rename_files()

        logger.info(f'整理完成，相关文件已保存到: {movie.save_dir}\n')

        # return str(all_info)
        # zip_file(os.path.join(movie.save_dir, cfg.NamingRule.output_folder), f'{dvdid}.zip')
        # zip_file(movie.save_dir, f'{dvdid}.zip')
        # shutil.rmtree(movie.save_dir)
        return send_from_directory(r".", f'{dvdid}.zip', as_attachment=True)
    except:
        pass

    if request.method != 'GET':
        return ""

    fullpath = request.args.get('q')
    dvdid = get_id(fullpath)
    logging.info(f"从文件{fullpath}中解析出{dvdid}")

    movies = {
        "data": [{"id": "2430", "number": "HEYZO-2430", "title": "オナりまくってグチョグチョ！なドすけべ娘と絶頂性交Vol.10", "provider": "HEYZO",
                  "homepage": "https://www.heyzo.com/moviepages/2430/index.html",
                  "thumb_url": "https://www.heyzo.com/contents/3000/2430/images/player_thumbnail.jpg",
                  "cover_url": "https://www.heyzo.com/contents/3000/2430/images/player_thumbnail.jpg", "score": 3.6,
                  "actors": ["百多えみり"], "release_date": "2021-01-03T00:00:00Z"},
                 {"id": "HEYZO-2430", "number": "HEYZO-2430", "title": "オナりまくってグチョグチョ！なドすけべ娘と絶頂性交Vol.10",
                  "provider": "JavBus", "homepage": "https://www.javbus.com/ja/HEYZO-2430",
                  "thumb_url": "https://www.javbus.com/imgs/thumbs/1ct1.jpg",
                  "cover_url": "https://www.javbus.com/imgs/cover/1ct1_b.jpg", "score": 0,
                  "release_date": "2021-01-03T00:00:00Z"},
                 {"id": "HEYZO-2430", "number": "HEYZO-2430", "title": "オナりまくってグチョグチョ！なドすけべ娘と絶頂性交Vol.10 百多えみり",
                  "provider": "AIRAV", "homepage": "https://www.airav.wiki/video/HEYZO-2430",
                  "thumb_url": "https://wiki-img.airav.wiki/storage/big_pic/99-07-20418.jpg",
                  "cover_url": "https://wiki-img.airav.wiki/storage/big_pic/99-07-20418.jpg", "score": 0,
                  "release_date": "0001-01-01T00:00:00Z"},
                 {"id": "heyzo2430", "number": "HEYZO-2430", "title": "オナりまくってグチョグチョ！なドすけべ娘と絶頂性交Vol.10",
                  "provider": "JAV321", "homepage": "https://www.jav321.com/video/heyzo2430",
                  "thumb_url": "https://www.jav321.com/contents/3000/2430/images/thumbnail.jpg",
                  "cover_url": "https://www.jav321.com/contents/3000/2430/images/player_thumbnail.jpg", "score": 0,
                  "release_date": "0001-01-01T00:00:00Z"}]}
    return json.dumps(movies)
    '''


@app.route('/get', methods=['GET', 'POST'])
def get_nfo():
    def check_step(result, msg='步骤错误'):
        """检查一个整理步骤的结果，并负责更新tqdm的进度"""
        if not result:
            raise Exception(msg)

    try:
        if request.method == 'GET':
            fullpath = request.args.get('path')
            dvdid = get_id(fullpath)
            logging.info(f"从文件{fullpath}中解析出{dvdid}")

            movie = Movie(dvdid)

            all_info = parallel_crawler(movie)
            logger.info('汇总数据')
            has_required_keys = info_summary(movie, all_info)
            check_step(has_required_keys, '抓取电影内容失败')

            generate_names(movie)
            check_step(movie.save_dir, '无法按命名规则生成目标文件夹')

            logger.info('下载封面图片')
            if not os.path.exists(movie.save_dir):
                os.makedirs(movie.save_dir)

            if cfg.Picture.use_big_cover:
                cover_dl = download_cover(movie.info.covers, movie.fanart_file, movie.info.big_covers)
            else:
                cover_dl = download_cover(movie.info.covers, movie.fanart_file)
            check_step(cover_dl, '下载封面图片失败')
            cover, pic_path = cover_dl
            # 确保实际下载的封面的url与即将写入到movie.info中的一致
            if cover != movie.info.cover:
                movie.info.cover = cover
            # 根据实际下载的封面的格式更新fanart/poster等图片的文件名
            if pic_path != movie.fanart_file:
                movie.fanart_file = pic_path
                actual_ext = os.path.splitext(pic_path)[1]
                movie.poster_file = os.path.splitext(movie.poster_file)[0] + actual_ext

            if cfg.Picture.use_ai_crop and (
                    movie.info.uncensored or
                    movie.data_src == 'fc2' or
                    movie.info.label.upper() in cfg.Picture.use_ai_crop_labels or
                    (R'\d' in cfg.Picture.use_ai_crop_labels and re.match(r'(\d{6}[-_]\d{3})', movie.info.dvdid))):
                method = cfg.Picture.ai_engine
                logger.info('使用AI裁剪海报封面')
            else:
                logger.info('裁剪海报封面')
                method = 'normal'
            crop_poster_wrapper(movie.fanart_file, movie.poster_file, method)

            if 'video_station' in cfg.NamingRule.media_servers:
                postStep_videostation(movie)
            if len(movie.files) > 1:
                postStep_MultiMoviePoster(movie)

            logger.info('写入NFO')
            write_nfo(movie.info, movie.nfo_file)

            for key, value in all_info.items():
                value.dump(os.path.join(movie.save_dir, f'{dvdid}_{key}.json'))
            movie.info.dump(os.path.join(movie.save_dir, f'{dvdid}.json'))

            logger.info('移动影片文件')
            movie.rename_files()

            logger.info(f'整理完成，相关文件已保存到: {movie.save_dir}\n')

            # return str(all_info)
            # zip_file(os.path.join(movie.save_dir, cfg.NamingRule.output_folder), f'{dvdid}.zip')
            zip_file(movie.save_dir, f'{dvdid}.zip')
            shutil.rmtree(movie.save_dir)
            return send_from_directory(r".", f'{dvdid}.zip', as_attachment=True)
    except:
        pass


if __name__ == '__main__':
    import_crawlers(cfg)
    app.run(host="0.0.0.0", port=environ.get("PORT", 5000))
