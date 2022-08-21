"""获取和转换影片的各类番号（DVD ID, DMM cid, DMM pid）"""
import os
import re
import sys

__all__ = ['get_id', 'guess_av_type']

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from core.config import cfg


def get_id(filepath: str) -> str:
    """从给定的文件路径中提取番号（DVD ID）"""
    # 通常是接收文件的路径，当然如果是普通字符串也可以
    filename = os.path.basename(filepath)
    filename = cfg.MovieID.ignore_pattern.sub('', filename)
    filename_lc = filename.lower()
    if 'fc2' in filename_lc:
        # 根据FC2 Club的影片数据，FC2编号为5-7个数字
        match = re.search(r'fc2[^a-z\d]{0,5}(ppv[^a-z\d]{0,5})?(\d{5,7})', filename, re.I)
        if match:
            return 'FC2-' + match.group(2)
    elif 'heydouga' in filename_lc:
        match = re.search(r'(heydouga)[-_]*(\d{4})[-_]0?(\d{3,5})', filename, re.I)
        if match:
            return '-'.join(match.groups())
    elif '1pon' in filename_lc or 'carib' in filename_lc:
        match = re.search(r'(\d{6})[-_](\d{3})', filename, re.I)
        if match:
            return '-'.join(match.groups())
    else:
        # 先尝试移除可疑域名进行匹配，如果匹配不到再使用原始文件名进行匹配
        no_domain = re.sub(r'\w{3,10}\.(com|net|app|xyz|org)', '', filename, flags=re.I)
        if no_domain != filename:
            avid = get_id(no_domain)
            if avid:
                return avid
        # 匹配缩写成hey的heydouga影片。由于番号分三部分，要先于后面分两部分的进行匹配
        match = re.search(r'(?:hey)[-_]*(\d{4})[-_]0?(\d{3,5})', filename, re.I)
        if match:
            return 'heydouga-' + '-'.join(match.groups())
        # 普通番号，优先尝试匹配带分隔符的（如ABC-123）
        match = re.search(r'([a-z]{2,10})[-_](\d{2,5})', filename, re.I)
        if match:
            return match.group(1) + '-' + match.group(2)
        # 普通番号，运行到这里时表明无法匹配到带分隔符的番号
        # 先尝试匹配东热的red, sky, ex三个不带-分隔符的系列
        # （这三个系列已停止更新，因此根据其作品编号将数字范围限制得小一些以降低误匹配概率）
        match = re.search(r'(red[01]\d\d|sky[0-3]\d\d|ex00[01]\d)', filename, re.I)
        if match:
            return match.group(1)
        # 然后再将影片视作缺失了-分隔符来匹配
        match = re.search(r'([a-z]{2,})(\d{2,5})', filename, re.I)
        if match:
            return match.group(1) + '-' + match.group(2)
    # 尝试匹配TMA制作的影片（如'T28-557'，他家的番号很乱）
    match = re.search(r'(T28[-_]\d{3})', filename)
    if match:
        return match.group(1)
    # 尝试匹配东热n, k系列
    match = re.search(r'(n\d{4}|k\d{4})', filename, re.I)
    if match:
        return match.group(1)
    # 尝试匹配纯数字番号（无码影片）
    match = re.search(r'(\d{6}[-_]\d{2,3})', filename)
    if match:
        return match.group(1)
    # 如果还是匹配不了，尝试将')('替换为'-'后再试，少部分影片的番号是由')('分隔的
    if ')(' in filepath:
        avid = get_id(filepath.replace(')(', '-'))
        if avid:
            return avid
    # 如果最后仍然匹配不了番号，则尝试使用文件所在文件夹的名字去匹配
    if os.path.isfile(filepath):
        norm = os.path.normpath(filepath)
        folder = norm.split(os.sep)[-2]
        return get_id(folder)
    return ''


def guess_av_type(avid: str) -> str:
    """识别给定的番号所属的分类: normal, fc2, cid"""
    match = re.match(r'^FC2-\d{5,7}$', avid, re.I)
    if match:
        return 'fc2'
    # 如果传入的avid完全匹配cid的模式，则将影片归类为cid
    # cid = get_cid(avid)
    # if cid == avid:
    #    return 'cid'
    # 以上都不是: 默认归类为normal
    return 'normal'


if __name__ == "__main__":
    import sys
    import pretty_errors

    pretty_errors.configure(display_link=True)
    if len(sys.argv) <= 1:
        avid = get_id('ex0001')
        # cid = get_cid('403ksxa54363_1')
        # print(avid, cid)
    else:
        for file in sys.argv[1:]:
            avid = get_id(file)
            if avid != '':
                print(f'{avid}\t{file}')