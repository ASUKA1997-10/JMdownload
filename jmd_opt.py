"""
jm助手 v2 - jmcomic 图形界面搜索下载工具 (优化版)

优化内容:
  1. 批量并行下载 + 进度回调      — download_photo([id…], option, callback=…)
  2. 专辑详情缓存                — _album_cache 避免重复请求
  3. 细化错误捕获                — MissingAlbumPhotoException / PartialDownloadFailedException 等
  4. 代码去重                   — _get_search_params() / _get_rankings_params()
  5. "下载整本"按钮              — 章节 tab 一键添加全部到下载队列
  6. 补充缺失分类                — MEIMAN / DOUJIN_COSPLAY / ENGLISH_SITE
  7. 搜索结果后台预加载           — 显示第 N 页时后台拉取第 N+1 页
  8. 登录 / 收藏夹浏览            — 新增登录 tab + 收藏 tab
  9. 下载进度条                  — 基于 callback 的实时进度
 10. 封面缩略图                  — 专辑详情面板展示封面
"""
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import threading
import queue
import pathlib
import io
import os
import tempfile

try:
    from PIL import Image, ImageTk
except ImportError:
    Image, ImageTk = (None,) * 2

from jmcomic import (
    JmOption,
    download_photo,
    download_album as _download_album,
    JmcomicException,
    JmcomicText,
    JmMagicConstants,
    Feature,
    MissingAlbumPhotoException,
    PartialDownloadFailedException,
    RequestRetryAllFailException,
)

_PAD_X = 5
_PAD_X_SM = 2
_PAD_Y = 5
_COMBO_WIDTH = 10

FEATURES = {
    'pdf': None,
    'zip': None,
    'long_img': None,
}
FORMAT_LABELS = {
    'pdf': 'PDF', 'zip': 'ZIP', 'long_img': '长图PNG',
}
ORDER_LABELS = {
    'mr': '最新', 'mv': '最多观看', 'tf': '最多喜欢',
    'tr': '最高评分', 'mp': '最多图片', 'md': '最多评论',
}
TIME_LABELS = {
    'a': '全部', 't': '今天', 'w': '本周', 'm': '本月',
}
CATEGORY_LABELS = {
    '0': '全部', 'hanman': '汉化', 'doujin': '同人',
    'single': '单行本', 'short': '短篇', 'another': '其他', '3d': '3D',
    'meiman': '美漫', 'doujin_cosplay': 'Cosplay同人', 'english_site': '英文',
}
SEARCH_TYPE_LABELS = {
    'site': '站内', 'work': '作品', 'author': '作者',
    'tag': '标签', 'actor': '角色',
}
SUB_CATEGORY_LABELS = {
    '': '无', 'chinese': '汉化', 'japanese': '日语',
    'cg': 'CG', 'youth': '青年', '3d': '3D',
    'cosplay': 'Cosplay', 'other': '其他',
}
ORDER_KEYS = list(ORDER_LABELS.keys())
TIME_KEYS = list(TIME_LABELS.keys())
CAT_KEYS = list(CATEGORY_LABELS.keys())
SEARCH_TYPE_KEYS = list(SEARCH_TYPE_LABELS.keys())
SUB_CAT_KEYS = list(SUB_CATEGORY_LABELS.keys())

# 全局专辑缓存 (aid -> JmAlbumDetail)
_album_cache = {}

# 封面缓存 (aid -> tk.PhotoImage)
_cover_cache = {}

# 预加载中的页面集合 (防止重复预加载)
_preloading_pages = set()


class JmGUI:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title('jm助手 v2')
        self.root.geometry('950x780')
        self.root.minsize(750, 620)
        self.root.bind('<Control-q>', lambda e: self.root.destroy())
        self.root.protocol('WM_DELETE_WINDOW', self.root.destroy)

        self.download_dir = str(pathlib.Path.home() / 'Downloads')

        self.option = JmOption.default()
        self.option.dir_rule.base_dir = self.download_dir
        self.client = self.option.new_jm_client()

        self.order_by = JmMagicConstants.ORDER_BY_LATEST
        self.time = JmMagicConstants.TIME_ALL
        self.category = JmMagicConstants.CATEGORY_ALL

        # search state
        self._search_page = 1
        self._search_items = []
        self._search_page_count = 0
        self._search_keyword = ''

        # rankings state
        self._rk_page = 1
        self._rk_items = []
        self._rk_page_count = 0
        self._rk_total = 0

        # album state
        self._current_aid = None
        self._current_album = None
        self._episodes = []
        self._ep_page = 1
        self._ep_reversed = False
        self._ep_page_size = 20

        # download state
        self._download_queue = []
        self._dl_task = None
        self._dl_done = 0
        self._dl_total = 0
        # pid -> queue index 映射
        self._pid_to_idx = {}

        # favorites state
        self._fav_folders = []
        self._fav_current_folder = '0'
        self._fav_page = 1
        self._fav_page_count = 0
        self._fav_items = []

        self._result_queue = queue.Queue()

        self._setup_theme()
        self._init_features()
        self._build_ui()
        self._poll_queue()

    # ==================== 主题 ====================

    def _setup_theme(self):
        style = ttk.Style(self.root)
        style.theme_use('clam')
        dark_bg = '#1e1e1e'
        dark_fg = '#d4d4d4'
        dark_input = '#252526'
        dark_select = '#264f78'
        dark_button = '#0e639c'
        dark_border = '#333333'
        dark_status_bg = '#007acc'
        self.root.configure(background=dark_bg)
        style.configure('.', background=dark_bg, foreground=dark_fg,
                        fieldbackground=dark_input, selectbackground=dark_select,
                        selectforeground='#ffffff', borderwidth=0,
                        focuscolor=dark_select, lightcolor=dark_border,
                        darkcolor=dark_border)
        style.configure('TFrame', background=dark_bg)
        style.configure('TLabel', background=dark_bg, foreground=dark_fg)
        style.configure('TButton', background=dark_button, foreground='#ffffff',
                        bordercolor=dark_border, focuscolor=dark_select)
        style.map('TButton', background=[('active', '#1a85c9'), ('pressed', '#005a9e'),
                                          ('disabled', '#3a3a3a')])
        style.configure('TEntry', fieldbackground=dark_input, foreground=dark_fg,
                        bordercolor=dark_border)
        style.configure('TCombobox', fieldbackground=dark_input, foreground=dark_fg,
                        bordercolor=dark_border, arrowcolor=dark_fg)
        style.map('TCombobox', fieldbackground=[('readonly', dark_input)])
        style.configure('TSeparator', background=dark_border)
        style.configure('Treeview', background=dark_input, foreground=dark_fg,
                        fieldbackground=dark_input, bordercolor=dark_border)
        style.configure('Treeview.Heading', background='#2d2d2d', foreground=dark_fg,
                        bordercolor=dark_border, relief='flat')
        style.map('Treeview', background=[('selected', dark_select)],
                  foreground=[('selected', '#ffffff')])
        style.configure('TSpinbox', fieldbackground=dark_input, foreground=dark_fg,
                        bordercolor=dark_border)
        style.configure('TLabelframe', background=dark_bg, foreground=dark_fg,
                        bordercolor=dark_border)
        style.configure('TLabelframe.Label', background=dark_bg, foreground=dark_fg)
        style.configure('Horizontal.TScrollbar', background='#2d2d2d',
                        bordercolor=dark_border, arrowcolor=dark_fg,
                        troughcolor=dark_input)
        style.configure('Vertical.TScrollbar', background='#2d2d2d',
                        bordercolor=dark_border, arrowcolor=dark_fg,
                        troughcolor=dark_input)
        style.configure('TNotebook', background=dark_bg, bordercolor=dark_border)
        style.configure('TNotebook.Tab', background='#2d2d2d', foreground=dark_fg,
                        bordercolor=dark_border)
        style.map('TNotebook.Tab', background=[('selected', dark_button)],
                  foreground=[('selected', '#ffffff')])
        style.configure('TCheckbutton', background=dark_bg, foreground=dark_fg)
        style.configure('TProgressbar', background=dark_button, troughcolor=dark_input,
                        bordercolor=dark_border)
        style.configure('StatusBar.TLabel', background=dark_status_bg,
                        foreground='#ffffff', relief='sunken')
        style.configure('AlbumInfo.TLabel', background=dark_bg, foreground=dark_fg,
                        font=('', 11, 'bold'))
        style.configure('LoginStatus.TLabel', background=dark_bg, foreground='#4ec9b0',
                        font=('', 9))
        style.configure('Cover.TLabel', background=dark_input)

    # ==================== 参数去重 ====================

    def _get_search_params(self):
        return (
            SEARCH_TYPE_KEYS[self.stype_cb.current()],
            ORDER_KEYS[self.sort_cb.current()],
            TIME_KEYS[self.time_cb.current()],
            CAT_KEYS[self.category_cb.current()],
            SUB_CAT_KEYS[self.subcat_cb.current()] or None,
        )

    def _get_rankings_params(self):
        return (
            CAT_KEYS[self.rk_cat_cb.current()],
            TIME_KEYS[self.rk_time_cb.current()],
            ORDER_KEYS[self.rk_sort_cb.current()],
            SUB_CAT_KEYS[self.rk_subcat_cb.current()] or None,
        )

    # ==================== 专辑缓存 ====================

    def _get_album_cached(self, aid):
        if aid in _album_cache:
            return _album_cache[aid]
        album = self.client.get_album_detail(aid)
        _album_cache[aid] = album
        return album

    # ==================== 初始化 ====================

    def _init_features(self):
        FEATURES['pdf'] = Feature.export_pdf(delete_original_file=True)
        FEATURES['zip'] = Feature.export_zip(delete_original_file=True)
        FEATURES['long_img'] = Feature.export_long_img()

    def _build_ui(self):
        self._build_bottom_bar()
        self._build_notebook()

    def _build_bottom_bar(self):
        bottom_frame = ttk.Frame(self.root)
        bottom_frame.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_var = tk.StringVar(value='就绪')
        status_bar = ttk.Label(bottom_frame, textvariable=self.status_var,
                               relief=tk.SUNKEN, anchor=tk.W, style='StatusBar.TLabel')
        status_bar.pack(side=tk.LEFT, fill=tk.X, expand=True)
        quit_btn = ttk.Button(bottom_frame, text='退出', command=self.root.destroy)
        quit_btn.pack(side=tk.RIGHT, padx=_PAD_X)

    def _build_notebook(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=_PAD_X, pady=_PAD_Y)
        self._build_search_tab()
        self._build_chapter_tab()
        self._build_download_tab()
        self._build_rankings_tab()
        self._build_favorites_tab()
        self._build_login_tab()

    def _combobox(self, parent, values, default=0, width=_COMBO_WIDTH):
        cb = ttk.Combobox(parent, values=values, state='readonly', width=width)
        cb.current(default)
        return cb

    # ==================== Tab 1: 搜索 ====================

    def _build_search_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='搜索')
        tab.columnconfigure(0, weight=1)

        search_bar_frame = ttk.Frame(tab)
        search_bar_frame.grid(row=0, column=0, sticky=tk.EW, padx=_PAD_X, pady=(_PAD_Y, 0))
        search_bar_frame.columnconfigure(5, weight=1)

        ttk.Label(search_bar_frame, text='搜索类型:').grid(row=0, column=0, padx=_PAD_X_SM)
        self.stype_cb = self._combobox(search_bar_frame, list(SEARCH_TYPE_LABELS.values()))
        self.stype_cb.grid(row=0, column=1, padx=_PAD_X_SM)

        ttk.Separator(search_bar_frame, orient=tk.VERTICAL).grid(
            row=0, column=2, padx=_PAD_X_SM, sticky=tk.NS)

        ttk.Label(search_bar_frame, text='关键词:').grid(row=0, column=4, padx=_PAD_X_SM)
        self.search_entry = ttk.Entry(search_bar_frame)
        self.search_entry.grid(row=0, column=5, sticky=tk.EW, padx=_PAD_X_SM)
        self.search_entry.bind('<Return>', lambda e: self.do_search())
        ttk.Button(search_bar_frame, text='搜索', command=self.do_search).grid(
            row=0, column=6, padx=_PAD_X_SM)

        ttk.Separator(search_bar_frame, orient=tk.VERTICAL).grid(
            row=0, column=7, padx=_PAD_X, sticky=tk.NS)

        ttk.Label(search_bar_frame, text='ID:').grid(row=0, column=8, padx=_PAD_X_SM)
        self.id_entry = ttk.Entry(search_bar_frame, width=12)
        self.id_entry.grid(row=0, column=9, padx=_PAD_X_SM)
        self.id_entry.bind('<Return>', lambda e: self.do_id_lookup())
        ttk.Button(search_bar_frame, text='直查', command=self.do_id_lookup).grid(
            row=0, column=10, padx=_PAD_X_SM)

        filter_frame = ttk.Frame(tab)
        filter_frame.grid(row=1, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_X_SM)
        filter_frame.columnconfigure(9, weight=1)

        ttk.Label(filter_frame, text='排序:').grid(row=0, column=0, padx=_PAD_X_SM)
        self.sort_cb = self._combobox(filter_frame, list(ORDER_LABELS.values()))
        self.sort_cb.grid(row=0, column=1, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='时间:').grid(row=0, column=2, padx=_PAD_X_SM)
        self.time_cb = self._combobox(filter_frame, list(TIME_LABELS.values()))
        self.time_cb.grid(row=0, column=3, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='分类:').grid(row=0, column=4, padx=_PAD_X_SM)
        self.category_cb = self._combobox(filter_frame, list(CATEGORY_LABELS.values()))
        self.category_cb.grid(row=0, column=5, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='副分类:').grid(row=0, column=6, padx=_PAD_X_SM)
        self.subcat_cb = self._combobox(filter_frame, list(SUB_CATEGORY_LABELS.values()))
        self.subcat_cb.grid(row=0, column=7, padx=_PAD_X_SM)

        ttk.Button(filter_frame, text='应用筛选', command=self._apply_filter).grid(
            row=0, column=8, padx=_PAD_X_SM)

        result_frame = ttk.Frame(tab)
        result_frame.grid(row=2, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
        tab.rowconfigure(2, weight=1)
        result_frame.columnconfigure(0, weight=1)
        result_frame.rowconfigure(0, weight=1)

        self.search_tree = ttk.Treeview(result_frame, columns=('idx', 'aid', 'title'),
                                        show='headings', height=15)
        self.search_tree.heading('idx', text='#')
        self.search_tree.heading('aid', text='JM ID')
        self.search_tree.heading('title', text='标题')
        self.search_tree.column('idx', width=40, anchor=tk.CENTER)
        self.search_tree.column('aid', width=80, anchor=tk.CENTER)
        self.search_tree.column('title', width=500)
        self.search_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.search_tree.bind('<Double-1>', lambda e: self._on_search_double_click())

        scroll = ttk.Scrollbar(result_frame, orient=tk.VERTICAL,
                               command=self.search_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.search_tree.configure(yscrollcommand=scroll.set)

        pager_frame = ttk.Frame(tab)
        pager_frame.grid(row=3, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.search_prev_btn = ttk.Button(pager_frame, text='上一页',
                                          command=self._search_prev)
        self.search_prev_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.search_page_var = tk.StringVar(value='第 0/0 页')
        ttk.Label(pager_frame, textvariable=self.search_page_var).pack(
            side=tk.LEFT, padx=10)

        self.search_next_btn = ttk.Button(pager_frame, text='下一页',
                                          command=self._search_next)
        self.search_next_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.search_total_var = tk.StringVar(value='共 0 条')
        ttk.Label(pager_frame, textvariable=self.search_total_var).pack(
            side=tk.LEFT, padx=10)

        ttk.Button(pager_frame, text='查看章节',
                   command=self._on_search_double_click).pack(side=tk.RIGHT, padx=_PAD_X)

    # ==================== Tab 2: 章节 ====================

    def _build_chapter_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='章节')
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(3, weight=1)

        self.album_info_var = tk.StringVar(value='未选择专辑')
        ttk.Label(tab, textvariable=self.album_info_var, style='AlbumInfo.TLabel').grid(
            row=0, column=0, sticky=tk.W, padx=_PAD_X, pady=(_PAD_Y, 0))

        self._album_detail_visible = False
        self._album_detail_frame = ttk.LabelFrame(tab, text='专辑详情')
        self._album_detail_frame.grid(row=1, column=0, sticky=tk.EW,
                                       padx=_PAD_X, pady=_PAD_X_SM)
        self._album_detail_frame.columnconfigure(1, weight=1)

        detail_top = ttk.Frame(self._album_detail_frame)
        detail_top.pack(fill=tk.X, padx=_PAD_X, pady=(_PAD_Y, 1))

        self._cover_label = ttk.Label(detail_top, style='Cover.TLabel')
        self._cover_label.pack(side=tk.LEFT, padx=(0, _PAD_X))

        detail_meta = ttk.Frame(detail_top)
        detail_meta.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        line1 = ttk.Frame(detail_meta)
        line1.pack(fill=tk.X, pady=1)
        self._detail_authors = ttk.Label(line1, text='作者: ')
        self._detail_authors.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_works = ttk.Label(line1, text='作品: ')
        self._detail_works.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_actors = ttk.Label(line1, text='角色: ')
        self._detail_actors.pack(side=tk.LEFT, padx=(0, 10))

        line2 = ttk.Frame(detail_meta)
        line2.pack(fill=tk.X, pady=1)
        self._detail_tags = ttk.Label(line2, text='标签: ')
        self._detail_tags.pack(side=tk.LEFT)

        line3 = ttk.Frame(detail_meta)
        line3.pack(fill=tk.X, pady=1)
        self._detail_views = ttk.Label(line3, text='观看: ')
        self._detail_views.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_likes = ttk.Label(line3, text='喜欢: ')
        self._detail_likes.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_comments = ttk.Label(line3, text='评论: ')
        self._detail_comments.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_pages = ttk.Label(line3, text='总页数: ')
        self._detail_pages.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_pub = ttk.Label(line3, text='发布: ')
        self._detail_pub.pack(side=tk.LEFT, padx=(0, 10))
        self._detail_update = ttk.Label(line3, text='更新: ')
        self._detail_update.pack(side=tk.LEFT)

        desc_frame = ttk.Frame(self._album_detail_frame)
        desc_frame.pack(fill=tk.X, padx=_PAD_X, pady=(1, 3))
        desc_frame.columnconfigure(0, weight=1)
        self._detail_desc = tk.Text(desc_frame, height=3, wrap=tk.WORD, font=('', 9),
                                    bg='#252526', fg='#d4d4d4',
                                    insertbackground='#d4d4d4',
                                    relief='flat', borderwidth=0)
        self._detail_desc.grid(row=0, column=0, sticky=tk.EW)
        desc_scroll = ttk.Scrollbar(desc_frame, orient=tk.VERTICAL,
                                    command=self._detail_desc.yview)
        desc_scroll.grid(row=0, column=1, sticky=tk.NS)
        self._detail_desc.configure(yscrollcommand=desc_scroll.set)

        chapter_toolbar = ttk.Frame(tab)
        chapter_toolbar.grid(row=2, column=0, sticky=tk.EW, padx=_PAD_X)

        self._ch_detail_btn = ttk.Button(chapter_toolbar, text='显示详情',
                                         command=self._ch_toggle_detail, width=9)
        self._ch_detail_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self._hide_album_detail()

        ttk.Button(chapter_toolbar, text='全选',
                   command=self._ch_select_all).pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(chapter_toolbar, text='反选',
                   command=self._ch_invert_selection).pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.ch_multi_var = tk.BooleanVar(value=False)
        self.ch_multi_cb = ttk.Checkbutton(chapter_toolbar, text='多选模式',
                                           variable=self.ch_multi_var,
                                           command=self._ch_toggle_multi)
        self.ch_multi_cb.pack(side=tk.LEFT, padx=10)

        ttk.Button(chapter_toolbar, text='下载整本',
                   command=self._ch_download_album).pack(side=tk.RIGHT, padx=_PAD_X)
        ttk.Button(chapter_toolbar, text='加入下载队列',
                   command=self._ch_add_to_queue).pack(side=tk.RIGHT, padx=_PAD_X)

        chapter_list_frame = ttk.Frame(tab)
        chapter_list_frame.grid(row=3, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
        chapter_list_frame.columnconfigure(0, weight=1)
        chapter_list_frame.rowconfigure(0, weight=1)

        self.ch_tree = ttk.Treeview(chapter_list_frame, columns=('idx', 'name', 'pid'),
                                    show='headings', height=15, selectmode='none')
        self.ch_tree.heading('idx', text='#')
        self.ch_tree.heading('name', text='章节名称')
        self.ch_tree.heading('pid', text='ID')
        self.ch_tree.column('idx', width=40, anchor=tk.CENTER)
        self.ch_tree.column('name', width=400)
        self.ch_tree.column('pid', width=80, anchor=tk.CENTER)
        self.ch_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.ch_tree.tag_configure('selected', background='#264f78')
        self.ch_tree.tag_configure('unselected', background='')
        self.ch_tree.bind('<ButtonRelease-1>', self._ch_click_toggle)

        scroll = ttk.Scrollbar(chapter_list_frame, orient=tk.VERTICAL,
                               command=self.ch_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.ch_tree.configure(yscrollcommand=scroll.set)

        chapter_controls = ttk.Frame(tab)
        chapter_controls.grid(row=4, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.ch_prev_btn = ttk.Button(chapter_controls, text='上页',
                                      command=self._ch_prev)
        self.ch_prev_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.ch_page_var = tk.StringVar(value='第 0/0 页')
        ttk.Label(chapter_controls, textvariable=self.ch_page_var).pack(
            side=tk.LEFT, padx=10)

        self.ch_next_btn = ttk.Button(chapter_controls, text='下页',
                                      command=self._ch_next)
        self.ch_next_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.ch_order_btn = ttk.Button(chapter_controls, text='倒序',
                                       command=self._ch_toggle_order)
        self.ch_order_btn.pack(side=tk.LEFT, padx=10)

    def _show_album_detail(self):
        self._album_detail_frame.grid()
        self._album_detail_visible = True
        self._ch_detail_btn.configure(text='隐藏详情')

    def _hide_album_detail(self):
        self._album_detail_frame.grid_remove()
        self._album_detail_visible = False
        self._ch_detail_btn.configure(text='显示详情')

    def _ch_toggle_detail(self):
        if self._album_detail_visible:
            self._hide_album_detail()
        else:
            self._show_album_detail()

    def _populate_album_detail(self, album):
        authors = ', '.join(album.authors) if album.authors else '未知'
        works = ', '.join(album.works) if album.works else '无'
        actors = ', '.join(album.actors) if album.actors else '无'
        tags = ', '.join(album.tags) if album.tags else '无'
        self._detail_authors.configure(text=f'作者: {authors}')
        self._detail_works.configure(text=f'作品: {works}')
        self._detail_actors.configure(text=f'角色: {actors}')
        self._detail_tags.configure(text=f'标签: {tags}')
        self._detail_views.configure(text=f'观看: {album.views}')
        self._detail_likes.configure(text=f'喜欢: {album.likes}')
        self._detail_comments.configure(text=f'评论: {album.comment_count}')
        self._detail_pages.configure(text=f'总页数: {album.page_count}')
        self._detail_pub.configure(text=f'发布: {album.pub_date}')
        self._detail_update.configure(text=f'更新: {album.update_date}')
        self._detail_desc.configure(state=tk.NORMAL)
        self._detail_desc.delete('1.0', tk.END)
        desc = album.description or '无简介'
        self._detail_desc.insert('1.0', desc.strip())
        self._detail_desc.configure(state=tk.DISABLED)
        self._load_cover(album)
        self._show_album_detail()

    def _load_cover(self, album):
        """下载专辑封面缩略图 (存内存不落盘)"""
        aid = album.id
        if aid in _cover_cache:
            self._cover_label.configure(image=_cover_cache[aid])
            return
        if Image is None:
            self._cover_label.configure(text='[PIL 未安装]')
            return
        try:
            url = JmcomicText.get_album_cover_url(aid)
            resp = self.client.get_jm_image(url)
            if resp.is_success:
                img = Image.open(io.BytesIO(resp.content))
                img = img.resize((180, 250), Image.LANCZOS)
                photo = ImageTk.PhotoImage(img)
                _cover_cache[aid] = photo
                self._cover_label.configure(image=photo)
            else:
                self._cover_label.configure(text='[无封面]')
        except Exception:
            self._cover_label.configure(text='[封面加载失败]')

    # ==================== Tab 3: 下载管理 ====================

    def _build_download_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='下载管理')
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(1, weight=1)

        toolbar_frame = ttk.Frame(tab)
        toolbar_frame.grid(row=0, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)
        toolbar_frame.columnconfigure(3, weight=1)

        ttk.Label(toolbar_frame, text='导出格式:').pack(side=tk.LEFT, padx=_PAD_X_SM)
        self.fmt_cb = self._combobox(toolbar_frame, list(FORMAT_LABELS.values()))
        self.fmt_cb.pack(side=tk.LEFT, padx=_PAD_X_SM)

        ttk.Label(toolbar_frame, text='  下载目录:').pack(side=tk.LEFT, padx=_PAD_X)
        self.dir_var = tk.StringVar(value=self.download_dir)
        dir_label = ttk.Label(toolbar_frame, textvariable=self.dir_var)
        dir_label.pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(toolbar_frame, text='选择目录',
                   command=self._dl_choose_dir).pack(side=tk.LEFT, padx=_PAD_X_SM)

        dl_list_frame = ttk.Frame(tab)
        dl_list_frame.grid(row=1, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
        dl_list_frame.columnconfigure(0, weight=1)
        dl_list_frame.rowconfigure(0, weight=1)

        self.dl_tree = ttk.Treeview(dl_list_frame,
                                    columns=('album', 'chapter', 'status',
                                             'progress', 'detail'),
                                    show='headings', height=12, selectmode='none')
        self.dl_tree.heading('album', text='专辑')
        self.dl_tree.heading('chapter', text='章节')
        self.dl_tree.heading('status', text='状态')
        self.dl_tree.heading('progress', text='进度')
        self.dl_tree.heading('detail', text='详情')
        self.dl_tree.column('album', width=160)
        self.dl_tree.column('chapter', width=200)
        self.dl_tree.column('status', width=70, anchor=tk.CENTER)
        self.dl_tree.column('progress', width=60, anchor=tk.CENTER)
        self.dl_tree.column('detail', width=100)
        self.dl_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.dl_tree.tag_configure('selected', background='#264f78')
        self.dl_tree.tag_configure('unselected', background='')
        self.dl_tree.bind('<ButtonRelease-1>', self._dl_click_toggle)

        scroll = ttk.Scrollbar(dl_list_frame, orient=tk.VERTICAL,
                               command=self.dl_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.dl_tree.configure(yscrollcommand=scroll.set)

        progress_frame = ttk.Frame(tab)
        progress_frame.grid(row=2, column=0, sticky=tk.EW, padx=_PAD_X, pady=(0, _PAD_X_SM))
        self.dl_progress = ttk.Progressbar(progress_frame, mode='determinate')
        self.dl_progress.pack(fill=tk.X)
        self.dl_progress_var = tk.StringVar(value='就绪')
        ttk.Label(progress_frame, textvariable=self.dl_progress_var).pack(
            side=tk.LEFT, padx=_PAD_X_SM)

        button_frame = ttk.Frame(tab)
        button_frame.grid(row=3, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.dl_start_btn = ttk.Button(button_frame, text='开始下载',
                                       command=self._dl_start)
        self.dl_start_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        ttk.Button(button_frame, text='全部开始',
                   command=self._dl_start_all).pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(button_frame, text='清除已完成',
                   command=self._dl_clear_done).pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(button_frame, text='移除选中',
                   command=self._dl_remove_selected).pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.dl_multi_var = tk.BooleanVar(value=False)
        self.dl_multi_cb = ttk.Checkbutton(button_frame, text='多选模式',
                                           variable=self.dl_multi_var,
                                           command=self._dl_toggle_multi)
        self.dl_multi_cb.pack(side=tk.RIGHT, padx=_PAD_X_SM)

    # ==================== Tab 4: 排行榜 ====================

    def _build_rankings_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='排行榜')
        tab.columnconfigure(0, weight=1)

        filter_frame = ttk.Frame(tab)
        filter_frame.grid(row=0, column=0, sticky=tk.EW, padx=_PAD_X, pady=(_PAD_Y, 0))
        filter_frame.columnconfigure(9, weight=1)

        ttk.Label(filter_frame, text='分类:').grid(row=0, column=0, padx=_PAD_X_SM)
        self.rk_cat_cb = self._combobox(filter_frame, list(CATEGORY_LABELS.values()))
        self.rk_cat_cb.grid(row=0, column=1, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='时间:').grid(row=0, column=2, padx=_PAD_X_SM)
        self.rk_time_cb = self._combobox(filter_frame, list(TIME_LABELS.values()),
                                         default=3)
        self.rk_time_cb.grid(row=0, column=3, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='排序:').grid(row=0, column=4, padx=_PAD_X_SM)
        self.rk_sort_cb = self._combobox(filter_frame, list(ORDER_LABELS.values()),
                                         default=1)
        self.rk_sort_cb.grid(row=0, column=5, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='副分类:').grid(row=0, column=6, padx=_PAD_X_SM)
        self.rk_subcat_cb = self._combobox(filter_frame,
                                           list(SUB_CATEGORY_LABELS.values()))
        self.rk_subcat_cb.grid(row=0, column=7, padx=_PAD_X_SM)

        shortcuts = ttk.Frame(filter_frame)
        shortcuts.grid(row=0, column=8, padx=_PAD_X)
        ttk.Label(shortcuts, text='快捷:').pack(side=tk.LEFT, padx=(0, _PAD_X_SM))
        ttk.Button(shortcuts, text='日榜', width=4,
                   command=lambda: self._rk_quick('t', 'mv')).pack(
            side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(shortcuts, text='周榜', width=4,
                   command=lambda: self._rk_quick('w', 'mv')).pack(
            side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(shortcuts, text='月榜', width=4,
                   command=lambda: self._rk_quick('m', 'mv')).pack(
            side=tk.LEFT, padx=_PAD_X_SM)

        ttk.Button(filter_frame, text='浏览', command=self.do_rankings).grid(
            row=0, column=9, padx=_PAD_X_SM)

        result_frame = ttk.Frame(tab)
        result_frame.grid(row=1, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
        tab.rowconfigure(1, weight=1)
        result_frame.columnconfigure(0, weight=1)
        result_frame.rowconfigure(0, weight=1)

        self.rk_tree = ttk.Treeview(result_frame, columns=('idx', 'aid', 'title'),
                                    show='headings', height=15)
        self.rk_tree.heading('idx', text='#')
        self.rk_tree.heading('aid', text='JM ID')
        self.rk_tree.heading('title', text='标题')
        self.rk_tree.column('idx', width=40, anchor=tk.CENTER)
        self.rk_tree.column('aid', width=80, anchor=tk.CENTER)
        self.rk_tree.column('title', width=500)
        self.rk_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.rk_tree.bind('<Double-1>', lambda e: self._on_rk_double_click())

        scroll = ttk.Scrollbar(result_frame, orient=tk.VERTICAL,
                               command=self.rk_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.rk_tree.configure(yscrollcommand=scroll.set)

        pager_frame = ttk.Frame(tab)
        pager_frame.grid(row=2, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.rk_prev_btn = ttk.Button(pager_frame, text='上一页',
                                      command=self._rk_prev)
        self.rk_prev_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.rk_page_var = tk.StringVar(value='第 0/0 页')
        ttk.Label(pager_frame, textvariable=self.rk_page_var).pack(
            side=tk.LEFT, padx=10)

        self.rk_next_btn = ttk.Button(pager_frame, text='下一页',
                                      command=self._rk_next)
        self.rk_next_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.rk_total_var = tk.StringVar(value='共 0 条')
        ttk.Label(pager_frame, textvariable=self.rk_total_var).pack(
            side=tk.LEFT, padx=10)

        ttk.Button(pager_frame, text='查看章节',
                   command=self._on_rk_double_click).pack(side=tk.RIGHT, padx=_PAD_X)

    # ==================== Tab 5: 收藏夹 ====================

    def _build_favorites_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='收藏')
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(2, weight=1)

        toolbar = ttk.Frame(tab)
        toolbar.grid(row=0, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)
        ttk.Label(toolbar, text='收藏夹:').pack(side=tk.LEFT, padx=_PAD_X_SM)
        self.fav_folder_cb = ttk.Combobox(toolbar, values=['登录后加载...'],
                                          state='readonly', width=20)
        self.fav_folder_cb.pack(side=tk.LEFT, padx=_PAD_X_SM)
        self.fav_folder_cb.bind('<<ComboboxSelected>>',
                                lambda e: self._fav_switch_folder())
        ttk.Button(toolbar, text='刷新', command=self._load_favorites).pack(
            side=tk.LEFT, padx=_PAD_X_SM)
        self._fav_login_hint = ttk.Label(toolbar, text='请先登录',
                                         foreground='#888888')
        self._fav_login_hint.pack(side=tk.LEFT, padx=10)

        result_frame = ttk.Frame(tab)
        result_frame.grid(row=2, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
        result_frame.columnconfigure(0, weight=1)
        result_frame.rowconfigure(0, weight=1)

        self.fav_tree = ttk.Treeview(result_frame, columns=('aid', 'title'),
                                     show='headings', height=18)
        self.fav_tree.heading('aid', text='JM ID')
        self.fav_tree.heading('title', text='标题')
        self.fav_tree.column('aid', width=100, anchor=tk.CENTER)
        self.fav_tree.column('title', width=600)
        self.fav_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.fav_tree.bind('<Double-1>', lambda e: self._on_fav_double_click())

        scroll = ttk.Scrollbar(result_frame, orient=tk.VERTICAL,
                               command=self.fav_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.fav_tree.configure(yscrollcommand=scroll.set)

        pager = ttk.Frame(tab)
        pager.grid(row=3, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)
        self.fav_prev_btn = ttk.Button(pager, text='上一页',
                                       command=self._fav_prev)
        self.fav_prev_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)
        self.fav_page_var = tk.StringVar(value='第 0/0 页')
        ttk.Label(pager, textvariable=self.fav_page_var).pack(side=tk.LEFT, padx=10)
        self.fav_next_btn = ttk.Button(pager, text='下一页',
                                       command=self._fav_next)
        self.fav_next_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

    # ==================== Tab 6: 登录 ====================

    def _build_login_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='登录')

        form = ttk.LabelFrame(tab, text='JM 登录')
        form.pack(padx=30, pady=30, fill=tk.X)

        ttk.Label(form, text='用户名:').grid(row=0, column=0, padx=_PAD_X,
                                             pady=_PAD_Y, sticky=tk.E)
        self.login_user_entry = ttk.Entry(form, width=25)
        self.login_user_entry.grid(row=0, column=1, padx=_PAD_X, pady=_PAD_Y)

        ttk.Label(form, text='密  码:').grid(row=1, column=0, padx=_PAD_X,
                                             pady=_PAD_Y, sticky=tk.E)
        self.login_pass_entry = ttk.Entry(form, width=25, show='*')
        self.login_pass_entry.grid(row=1, column=1, padx=_PAD_X, pady=_PAD_Y)
        self.login_pass_entry.bind('<Return>', lambda e: self._do_login())

        btn_frame = ttk.Frame(form)
        btn_frame.grid(row=2, column=0, columnspan=2, pady=_PAD_Y)
        ttk.Button(btn_frame, text='登录', command=self._do_login).pack(
            side=tk.LEFT, padx=_PAD_X_SM)

        self.login_status_var = tk.StringVar(value='')
        ttk.Label(form, textvariable=self.login_status_var,
                  style='LoginStatus.TLabel').grid(
            row=3, column=0, columnspan=2, pady=_PAD_Y)

    # ==================== 快捷排行榜 ====================

    def _rk_quick(self, time_key, order_key):
        time_idx = TIME_KEYS.index(time_key)
        order_idx = ORDER_KEYS.index(order_key)
        self.rk_time_cb.current(time_idx)
        self.rk_sort_cb.current(order_idx)
        self.do_rankings()

    # ==================== 搜索 ====================

    def do_search(self):
        keyword = self.search_entry.get().strip()
        if not keyword:
            return
        self._search_keyword = keyword
        self._search_page = 1
        _preloading_pages.discard(('search', 2))
        self._set_status('搜索中...')
        self.search_tree.delete(*self.search_tree.get_children())
        self._search_items.clear()
        stype, order_val, time_val, cat_val, subcat_val = self._get_search_params()
        t = threading.Thread(
            target=self._search_worker,
            args=(keyword, 1, stype, order_val, time_val, cat_val, subcat_val),
            daemon=True,
        )
        t.start()

    def _search_worker(self, keyword, page, stype, order_val, time_val, cat_val,
                       subcat_val):
        try:
            search_map = {
                'site': self.client.search_site,
                'work': self.client.search_work,
                'author': self.client.search_author,
                'tag': self.client.search_tag,
                'actor': self.client.search_actor,
            }
            method = search_map.get(stype, self.client.search_site)
            result = method(
                search_query=keyword,
                page=page,
                order_by=order_val,
                time=time_val,
                category=cat_val,
                sub_category=subcat_val,
            )
            items = list(result.iter_id_title())
            self._result_queue.put(('search_result', {
                'items': items,
                'page': page,
                'page_count': result.page_count,
                'total': result.total,
            }))
        except MissingAlbumPhotoException:
            self._result_queue.put(('search_error',
                                    f'未找到: {keyword}'))
        except RequestRetryAllFailException as e:
            self._result_queue.put(('search_error',
                                    f'网络请求失败 (重试耗尽): {e}'))
        except JmcomicException as e:
            self._result_queue.put(('search_error', str(e)))
        except Exception as e:
            self._result_queue.put(('search_error', f'未知错误: {e}'))

    def _on_search_result(self, data):
        self._search_items = data['items']
        self._search_page = data['page']
        self._search_page_count = data['page_count']
        total = data['total']

        self.search_tree.delete(*self.search_tree.get_children())
        for i, (aid, title) in enumerate(data['items'], 1):
            self.search_tree.insert('', tk.END, values=(i, aid, title))

        self.search_page_var.set(
            f'第 {self._search_page}/{self._search_page_count} 页')
        self.search_total_var.set(f'共 {total} 条')
        self._update_search_nav()
        self._set_status(f'搜索完成，共 {total} 条结果')
        self._preload_search_next()

    def _update_search_nav(self):
        self.search_prev_btn.configure(
            state=tk.NORMAL if self._search_page > 1 else tk.DISABLED)
        self.search_next_btn.configure(
            state=tk.NORMAL if self._search_page < self._search_page_count
            else tk.DISABLED)

    def _search_prev(self):
        if not self._search_keyword or self._search_page <= 1:
            return
        self._search_page -= 1
        if self._search_page > 1:
            _preloading_pages.discard(('search', self._search_page + 1))
        self._set_status(f'搜索中 (第{self._search_page}页)...')
        self.search_tree.delete(*self.search_tree.get_children())
        stype, order_val, time_val, cat_val, subcat_val = self._get_search_params()
        t = threading.Thread(
            target=self._search_worker,
            args=(self._search_keyword, self._search_page, stype, order_val,
                  time_val, cat_val, subcat_val),
            daemon=True,
        )
        t.start()

    def _search_next(self):
        if not self._search_keyword or self._search_page >= self._search_page_count:
            return
        self._search_page += 1
        _preloading_pages.discard(('search', self._search_page))
        self._set_status(f'搜索中 (第{self._search_page}页)...')
        self.search_tree.delete(*self.search_tree.get_children())
        stype, order_val, time_val, cat_val, subcat_val = self._get_search_params()
        t = threading.Thread(
            target=self._search_worker,
            args=(self._search_keyword, self._search_page, stype, order_val,
                  time_val, cat_val, subcat_val),
            daemon=True,
        )
        t.start()

    def _preload_search_next(self):
        """后台预加载搜索结果下一页"""
        next_page = self._search_page + 1
        if next_page > self._search_page_count:
            return
        key = ('search', next_page)
        if key in _preloading_pages:
            return
        _preloading_pages.add(key)
        stype, order_val, time_val, cat_val, subcat_val = self._get_search_params()

        def _preload():
            try:
                search_map = {
                    'site': self.client.search_site,
                    'work': self.client.search_work,
                    'author': self.client.search_author,
                    'tag': self.client.search_tag,
                    'actor': self.client.search_actor,
                }
                method = search_map.get(stype, self.client.search_site)
                result = method(
                    search_query=self._search_keyword,
                    page=next_page,
                    order_by=order_val,
                    time=time_val,
                    category=cat_val,
                    sub_category=subcat_val,
                )
                items = list(result.iter_id_title())
                self._result_queue.put(('search_preload', {
                    'items': items,
                    'page': next_page,
                    'page_count': result.page_count,
                    'total': result.total,
                }))
            except Exception:
                pass
            finally:
                _preloading_pages.discard(key)

        threading.Thread(target=_preload, daemon=True).start()

    def _on_search_preload(self, data):
        preload_page = data['page']
        if preload_page != self._search_page:
            return
        self._search_items = data['items']
        self._search_page_count = data['page_count']
        self.search_tree.delete(*self.search_tree.get_children())
        for i, (aid, title) in enumerate(data['items'], 1):
            self.search_tree.insert('', tk.END, values=(i, aid, title))
        self.search_page_var.set(
            f'第 {self._search_page}/{self._search_page_count} 页')
        self.search_total_var.set(f'共 {data["total"]} 条')
        self._update_search_nav()
        self._set_status(
            f'(预加载) 第 {self._search_page}/{self._search_page_count} 页')
        self._preload_search_next()

    def _apply_filter(self):
        if self._search_keyword:
            self.do_search()
        else:
            self._set_status('筛选已更新')

    def do_id_lookup(self):
        aid = self.id_entry.get().strip()
        if not aid.isdigit():
            messagebox.showwarning('输入错误', 'ID 必须是数字')
            return
        self._set_status(f'查询 JM{aid}...')
        t = threading.Thread(target=self._id_lookup_worker, args=(aid,),
                             daemon=True)
        t.start()

    def _id_lookup_worker(self, aid):
        try:
            album = self._get_album_cached(aid)
            self._result_queue.put(('album_loaded', album))
        except MissingAlbumPhotoException:
            self._result_queue.put(('search_error', f'JM{aid} 不存在'))
        except JmcomicException as e:
            self._result_queue.put(('search_error',
                                    f'查询失败 JM{aid}: {str(e)}'))
        except Exception as e:
            self._result_queue.put(('search_error', f'未知错误: {e}'))

    def _on_album_loaded(self, album):
        title = album.name or album.title
        self._set_status(f'已加载 JM{album.id} - {title}')
        self._load_album(album)

    def _on_search_double_click(self):
        sel = self.search_tree.selection()
        if not sel:
            return
        values = self.search_tree.item(sel[0])['values']
        if len(values) < 2:
            return
        aid = values[1]
        self._set_status(f'加载 JM{aid}...')
        t = threading.Thread(target=self._search_lookup_worker, args=(aid,),
                             daemon=True)
        t.start()

    def _search_lookup_worker(self, aid):
        try:
            album = self._get_album_cached(aid)
            self._result_queue.put(('album_loaded', album))
        except MissingAlbumPhotoException:
            self._result_queue.put(('search_error', f'JM{aid} 不存在'))
        except RequestRetryAllFailException as e:
            self._result_queue.put(('search_error',
                                    f'网络请求失败 (重试耗尽): {e}'))
        except JmcomicException as e:
            self._result_queue.put(('search_error', f'获取专辑失败: {e}'))
        except Exception as e:
            self._result_queue.put(('search_error', f'未知错误: {e}'))

    def _load_album(self, album):
        self._current_aid = album.id
        self._current_album = album
        self._episodes = album.episode_list
        self._ep_page = 1
        self._ep_reversed = False
        self.ch_order_btn.configure(text='倒序')
        title = album.name or album.title
        self.album_info_var.set(f'JM{self._current_aid} - {title}')
        self._populate_album_detail(album)
        self._refresh_ch_page()
        self.notebook.select(1)

    # ==================== 排行榜 ====================

    def do_rankings(self):
        self._rk_page = 1
        _preloading_pages.discard(('rankings', 2))
        self._set_status('加载排行榜...')
        self.rk_tree.delete(*self.rk_tree.get_children())
        self._rk_items.clear()
        cat_val, time_val, order_val, subcat_val = self._get_rankings_params()
        t = threading.Thread(
            target=self._rankings_worker,
            args=(1, cat_val, time_val, order_val, subcat_val),
            daemon=True,
        )
        t.start()

    def _rankings_worker(self, page, cat_val, time_val, order_val, subcat_val):
        try:
            result = self.client.categories_filter(
                page=page,
                category=cat_val,
                time=time_val,
                order_by=order_val,
                sub_category=subcat_val,
            )
            items = list(result.iter_id_title())
            self._result_queue.put(('rankings_result', {
                'items': items,
                'page': page,
                'page_count': result.page_count,
                'total': result.total,
            }))
        except RequestRetryAllFailException as e:
            self._result_queue.put(('search_error',
                                    f'排行榜加载失败 (重试耗尽): {e}'))
        except JmcomicException as e:
            self._result_queue.put(('search_error', f'排行榜加载失败: {e}'))
        except Exception as e:
            self._result_queue.put(('search_error', f'未知错误: {e}'))

    def _on_rankings_result(self, data):
        self._rk_items = data['items']
        self._rk_page = data['page']
        self._rk_page_count = data['page_count']
        total = data['total']

        self.rk_tree.delete(*self.rk_tree.get_children())
        for i, (aid, title) in enumerate(data['items'], 1):
            self.rk_tree.insert('', tk.END, values=(i, aid, title))

        self.rk_page_var.set(f'第 {self._rk_page}/{self._rk_page_count} 页')
        self.rk_total_var.set(f'共 {total} 条')
        self._update_rk_nav()
        self._set_status(f'排行榜加载完成，共 {total} 条')
        self._preload_rankings_next()

    def _update_rk_nav(self):
        self.rk_prev_btn.configure(
            state=tk.NORMAL if self._rk_page > 1 else tk.DISABLED)
        self.rk_next_btn.configure(
            state=tk.NORMAL if self._rk_page < self._rk_page_count
            else tk.DISABLED)

    def _rk_prev(self):
        if self._rk_page <= 1:
            return
        self._rk_page -= 1
        _preloading_pages.discard(('rankings', self._rk_page + 1))
        self._set_status(f'加载排行 (第{self._rk_page}页)...')
        self.rk_tree.delete(*self.rk_tree.get_children())
        cat_val, time_val, order_val, subcat_val = self._get_rankings_params()
        t = threading.Thread(
            target=self._rankings_worker,
            args=(self._rk_page, cat_val, time_val, order_val, subcat_val),
            daemon=True,
        )
        t.start()

    def _rk_next(self):
        if self._rk_page >= self._rk_page_count:
            return
        self._rk_page += 1
        _preloading_pages.discard(('rankings', self._rk_page))
        self._set_status(f'加载排行 (第{self._rk_page}页)...')
        self.rk_tree.delete(*self.rk_tree.get_children())
        cat_val, time_val, order_val, subcat_val = self._get_rankings_params()
        t = threading.Thread(
            target=self._rankings_worker,
            args=(self._rk_page, cat_val, time_val, order_val, subcat_val),
            daemon=True,
        )
        t.start()

    def _preload_rankings_next(self):
        next_page = self._rk_page + 1
        if next_page > self._rk_page_count:
            return
        key = ('rankings', next_page)
        if key in _preloading_pages:
            return
        _preloading_pages.add(key)
        cat_val, time_val, order_val, subcat_val = self._get_rankings_params()

        def _preload():
            try:
                result = self.client.categories_filter(
                    page=next_page,
                    category=cat_val,
                    time=time_val,
                    order_by=order_val,
                    sub_category=subcat_val,
                )
                items = list(result.iter_id_title())
                self._result_queue.put(('rankings_preload', {
                    'items': items,
                    'page': next_page,
                    'page_count': result.page_count,
                    'total': result.total,
                }))
            except Exception:
                pass
            finally:
                _preloading_pages.discard(key)

        threading.Thread(target=_preload, daemon=True).start()

    def _on_rankings_preload(self, data):
        preload_page = data['page']
        if preload_page != self._rk_page:
            return
        self._rk_items = data['items']
        self._rk_page_count = data['page_count']
        self.rk_tree.delete(*self.rk_tree.get_children())
        for i, (aid, title) in enumerate(data['items'], 1):
            self.rk_tree.insert('', tk.END, values=(i, aid, title))
        self.rk_page_var.set(f'第 {self._rk_page}/{self._rk_page_count} 页')
        self.rk_total_var.set(f'共 {data["total"]} 条')
        self._update_rk_nav()
        self._set_status(
            f'(预加载) 第 {self._rk_page}/{self._rk_page_count} 页')
        self._preload_rankings_next()

    def _on_rk_double_click(self):
        sel = self.rk_tree.selection()
        if not sel:
            return
        values = self.rk_tree.item(sel[0])['values']
        if len(values) < 2:
            return
        aid = values[1]
        self._set_status(f'加载 JM{aid}...')
        t = threading.Thread(target=self._search_lookup_worker, args=(aid,),
                             daemon=True)
        t.start()

    # ==================== 章节 ====================

    def _ep_count(self):
        return len(self._episodes)

    def _get_ep(self, index):
        if self._ep_reversed:
            return self._episodes[self._ep_count() - 1 - index]
        return self._episodes[index]

    def _refresh_ch_page(self):
        total = self._ep_count()
        page_count = max(1, (total + self._ep_page_size - 1) // self._ep_page_size)
        if self._ep_page > page_count:
            self._ep_page = page_count

        start = (self._ep_page - 1) * self._ep_page_size
        end = min(start + self._ep_page_size, total)

        order = '倒序' if self._ep_reversed else '正序'
        self.ch_page_var.set(f'第 {self._ep_page}/{page_count} 页 ({order})')
        self.ch_prev_btn.configure(
            state=tk.NORMAL if self._ep_page > 1 else tk.DISABLED)
        self.ch_next_btn.configure(
            state=tk.NORMAL if self._ep_page < page_count else tk.DISABLED)

        self.ch_tree.delete(*self.ch_tree.get_children())
        for i in range(start, end):
            ep = self._get_ep(i)
            pid, pidx, ptitle = ep[0], ep[1], ep[2]
            label = ptitle if ptitle else f'章节{pidx}'
            self.ch_tree.insert('', tk.END, values=(i + 1, label, pid),
                                tags=('unselected',))

    def _ch_prev(self):
        if self._ep_page > 1:
            self._ep_page -= 1
            self._refresh_ch_page()

    def _ch_next(self):
        page_count = max(1, (self._ep_count() + self._ep_page_size - 1)
                         // self._ep_page_size)
        if self._ep_page < page_count:
            self._ep_page += 1
            self._refresh_ch_page()

    def _ch_toggle_order(self):
        self._ep_reversed = not self._ep_reversed
        self.ch_order_btn.configure(text='正序' if self._ep_reversed else '倒序')
        self._ep_page = 1
        self._refresh_ch_page()

    def _ch_toggle_multi(self):
        pass

    def _ch_click_toggle(self, event):
        item = self.ch_tree.identify_row(event.y)
        if not item:
            return
        if self.ch_multi_var.get():
            tags = self.ch_tree.item(item, 'tags')
            if 'selected' in tags:
                self.ch_tree.item(item, tags=('unselected',))
            else:
                self.ch_tree.item(item, tags=('selected',))
        else:
            for child in self.ch_tree.get_children():
                self.ch_tree.item(child, tags=('unselected',))
            self.ch_tree.item(item, tags=('selected',))

    def _ch_select_all(self):
        for item in self.ch_tree.get_children():
            self.ch_tree.item(item, tags=('selected',))

    def _ch_invert_selection(self):
        for item in self.ch_tree.get_children():
            tags = self.ch_tree.item(item, 'tags')
            self.ch_tree.item(item,
                              tags=('unselected',) if 'selected' in tags
                              else ('selected',))

    def _ch_add_to_queue(self):
        if not self._current_aid or not self._current_album:
            messagebox.showinfo('提示', '请先选择专辑')
            return
        title = self._current_album.name or self._current_album.title
        added = 0
        for item in self.ch_tree.get_children():
            if 'selected' not in self.ch_tree.item(item, 'tags'):
                continue
            values = self.ch_tree.item(item, 'values')
            idx = int(values[0]) - 1
            if 0 <= idx < self._ep_count():
                ep = self._get_ep(idx)
                pid, pidx, ptitle = ep[0], ep[1], ep[2]
                plabel = ptitle if ptitle else f'章节{pidx}'
                self._download_queue.append(
                    (self._current_aid, title, pid, plabel))
                added += 1
        if added > 0:
            self._refresh_dl_tree()
            self._set_status(f'已添加 {added} 个章节到下载队列')
            self.notebook.select(2)
        else:
            messagebox.showinfo('提示', '请先在章节列表中勾选要下载的章节')

    def _ch_download_album(self):
        """下载整本：把专辑所有章节加入队列并开始下载"""
        if not self._current_aid or not self._current_album:
            messagebox.showinfo('提示', '请先选择专辑')
            return
        title = self._current_album.name or self._current_album.title
        added = 0
        for ep in self._episodes:
            pid, pidx, ptitle = ep[0], ep[1], ep[2]
            plabel = ptitle if ptitle else f'章节{pidx}'
            self._download_queue.append((self._current_aid, title, pid, plabel))
            added += 1
        self._refresh_dl_tree()
        self._set_status(f'已添加整本 {added} 章节到下载队列，开始下载...')
        self.notebook.select(2)
        self._dl_start_all()

    # ==================== 下载管理 ====================

    def _refresh_dl_tree(self):
        self.dl_tree.delete(*self.dl_tree.get_children())
        for _, title, _, plabel in self._download_queue:
            self.dl_tree.insert('', tk.END, values=(title, plabel, '等待中', '', ''),
                                tags=('unselected',))

    def _dl_choose_dir(self):
        chosen = filedialog.askdirectory(initialdir=self.download_dir,
                                         title='选择下载目录')
        if chosen:
            self.download_dir = chosen
            self.option.dir_rule.base_dir = chosen
            self.dir_var.set(chosen)
            self._set_status(f'下载目录已切换: {chosen}')

    def _dl_start(self):
        if self._dl_task and self._dl_task.is_alive():
            self._set_status('下载任务进行中，请等待完成')
            return
        indices = self._dl_get_selected_indices()
        if not indices:
            messagebox.showinfo('提示', '请先在下载列表中选择要下载的项目')
            return
        fmt_key = list(FORMAT_LABELS.keys())[self.fmt_cb.current()]
        t = threading.Thread(target=self._download_worker,
                             args=(indices, fmt_key), daemon=True)
        self._dl_task = t
        t.start()

    def _dl_start_all(self):
        if self._dl_task and self._dl_task.is_alive():
            self._set_status('下载任务进行中，请等待完成')
            return
        if not self._download_queue:
            return
        all_indices = list(range(len(self._download_queue)))
        fmt_key = list(FORMAT_LABELS.keys())[self.fmt_cb.current()]
        t = threading.Thread(target=self._download_worker,
                             args=(all_indices, fmt_key), daemon=True)
        self._dl_task = t
        t.start()

    def _download_worker(self, indices, fmt_key):
        """批量并行下载"""
        photo_ids = []
        self._pid_to_idx.clear()
        for idx in sorted(indices):
            if idx < len(self._download_queue):
                pid = self._download_queue[idx][2]
                photo_ids.append(int(pid))
                self._pid_to_idx[str(pid)] = idx

        total = len(photo_ids)
        if total == 0:
            self._result_queue.put(('dl_done', None))
            return

        self._result_queue.put(('dl_progress_total', total))

        for pid in photo_ids:
            idx = self._pid_to_idx.get(str(pid))
            self._result_queue.put(
                ('dl_status', (idx, '下载中', f'0/{total}', pid)))

        done_count = [0]

        def _callback(photo, dler):
            pid = str(photo.photo_id)
            idx = self._pid_to_idx.get(pid)
            done_count[0] += 1
            self._result_queue.put(
                ('dl_status',
                 (idx, '已完成', f'{done_count[0]}/{total}', pid)))

        try:
            download_photo(
                photo_ids,
                self.option,
                extra=FEATURES[fmt_key],
                callback=_callback,
                check_exception=False,
            )
            self._result_queue.put(('dl_done', None))
        except PartialDownloadFailedException as e:
            self._result_queue.put(
                ('dl_done', f'部分下载失败 ({done_count[0]}/{total})'))
        except JmcomicException as e:
            self._result_queue.put(('dl_done', str(e)))
        except Exception as e:
            self._result_queue.put(('dl_done', f'未知错误: {e}'))

    def _dl_clear_done(self):
        to_remove = []
        for i, child in enumerate(self.dl_tree.get_children()):
            values = self.dl_tree.item(child, 'values')
            if len(values) >= 3 and values[2] == '已完成':
                to_remove.append(i)
        for i in reversed(to_remove):
            if i < len(self._download_queue):
                self._download_queue.pop(i)
        self._refresh_dl_tree()
        self._set_status(f'已清除 {len(to_remove)} 个已完成项')

    def _dl_remove_selected(self):
        indices = self._dl_get_selected_indices()
        if not indices:
            return
        for i in reversed(indices):
            if i < len(self._download_queue):
                self._download_queue.pop(i)
        self._refresh_dl_tree()
        self._set_status(f'已移除 {len(indices)} 项')

    def _dl_toggle_multi(self):
        pass

    def _dl_click_toggle(self, event):
        item = self.dl_tree.identify_row(event.y)
        if not item:
            return
        if self.dl_multi_var.get():
            tags = self.dl_tree.item(item, 'tags')
            if 'selected' in tags:
                self.dl_tree.item(item, tags=('unselected',))
            else:
                self.dl_tree.item(item, tags=('selected',))
        else:
            for child in self.dl_tree.get_children():
                self.dl_tree.item(child, tags=('unselected',))
            self.dl_tree.item(item, tags=('selected',))

    def _dl_get_selected_indices(self):
        indices = []
        for i, item in enumerate(self.dl_tree.get_children()):
            if 'selected' in self.dl_tree.item(item, 'tags'):
                indices.append(i)
        return indices

    # ==================== 登录 ====================

    def _do_login(self):
        username = self.login_user_entry.get().strip()
        password = self.login_pass_entry.get().strip()
        if not username or not password:
            self.login_status_var.set('请输入用户名和密码')
            return
        self.login_status_var.set('登录中...')

        def _login_worker():
            try:
                self.client.login(username, password)
                self._result_queue.put(('login_success', username))
            except JmcomicException as e:
                self._result_queue.put(('login_error', str(e)))
            except Exception as e:
                self._result_queue.put(('login_error', f'未知错误: {e}'))

        threading.Thread(target=_login_worker, daemon=True).start()

    def _on_login_success(self, username):
        self.login_status_var.set(f'已登录: {username}')
        self._set_status(f'登录成功: {username}')
        self._load_favorites()

    def _on_login_error(self, msg):
        self.login_status_var.set(f'登录失败: {msg}')
        self._set_status(f'登录失败: {msg}')

    # ==================== 收藏夹 ====================

    def _load_favorites(self):
        self._set_status('加载收藏夹...')

        def _worker():
            try:
                result = self.client.favorite_folder(page=1, folder_id='0')
                folders = list(result.iter_folder_id_name())
                items = list(result.iter_id_title())
                self._result_queue.put(('favorites_loaded', {
                    'folders': folders,
                    'items': items,
                    'page': 1,
                    'page_count': result.page_count,
                }))
            except JmcomicException as e:
                self._result_queue.put(('search_error', f'加载收藏失败: {e}'))
            except Exception as e:
                self._result_queue.put(('search_error', f'未知错误: {e}'))

        threading.Thread(target=_worker, daemon=True).start()

    def _on_favorites_loaded(self, data):
        self._fav_folders = data['folders']
        self._fav_items = data['items']
        self._fav_current_folder = '0'
        self._fav_page = data['page']
        self._fav_page_count = data['page_count']

        folder_names = [name for _, name in self._fav_folders]
        self.fav_folder_cb.configure(values=folder_names)
        if folder_names:
            self.fav_folder_cb.current(0)
        self._fav_login_hint.configure(text='')

        self.fav_tree.delete(*self.fav_tree.get_children())
        for aid, title in self._fav_items:
            self.fav_tree.insert('', tk.END, values=(aid, title))

        self.fav_page_var.set(
            f'第 {self._fav_page}/{self._fav_page_count} 页')
        self._set_status(
            f'收藏夹加载完成，共 {len(self._fav_folders)} 个收藏夹')

    def _fav_switch_folder(self):
        idx = self.fav_folder_cb.current()
        if idx < 0 or idx >= len(self._fav_folders):
            return
        folder_id, name = self._fav_folders[idx]
        self._fav_current_folder = folder_id
        self._fav_page = 1
        self._set_status(f'加载收藏夹: {name}...')
        threading.Thread(target=self._fav_page_worker, args=(1, folder_id),
                         daemon=True).start()

    def _fav_page_worker(self, page, folder_id):
        try:
            result = self.client.favorite_folder(page=page, folder_id=folder_id)
            items = list(result.iter_id_title())
            self._result_queue.put(('favorites_page', {
                'items': items,
                'page': page,
                'page_count': result.page_count,
            }))
        except JmcomicException as e:
            self._result_queue.put(('search_error', f'加载收藏页失败: {e}'))
        except Exception as e:
            self._result_queue.put(('search_error', f'未知错误: {e}'))

    def _on_favorites_page(self, data):
        self._fav_items = data['items']
        self._fav_page = data['page']
        self._fav_page_count = data['page_count']
        self.fav_tree.delete(*self.fav_tree.get_children())
        for aid, title in self._fav_items:
            self.fav_tree.insert('', tk.END, values=(aid, title))
        self.fav_page_var.set(
            f'第 {self._fav_page}/{self._fav_page_count} 页')
        folder_name = '收藏'
        idx = self.fav_folder_cb.current()
        if 0 <= idx < len(self._fav_folders):
            folder_name = self._fav_folders[idx][1]
        self._set_status(
            f'收藏夹 {folder_name}  第 {self._fav_page}/{self._fav_page_count} 页')

    def _fav_prev(self):
        if self._fav_page <= 1:
            return
        self._fav_page -= 1
        threading.Thread(target=self._fav_page_worker,
                         args=(self._fav_page, self._fav_current_folder),
                         daemon=True).start()

    def _fav_next(self):
        if self._fav_page >= self._fav_page_count:
            return
        self._fav_page += 1
        threading.Thread(target=self._fav_page_worker,
                         args=(self._fav_page, self._fav_current_folder),
                         daemon=True).start()

    def _on_fav_double_click(self):
        sel = self.fav_tree.selection()
        if not sel:
            return
        values = self.fav_tree.item(sel[0])['values']
        if len(values) < 1:
            return
        aid = values[0]
        self._set_status(f'加载 JM{aid}...')
        t = threading.Thread(target=self._search_lookup_worker, args=(aid,),
                             daemon=True)
        t.start()

    # ==================== 线程通信 ====================

    def _poll_queue(self):
        try:
            while True:
                msg_type, data = self._result_queue.get_nowait()
                self._handle_msg(msg_type, data)
        except queue.Empty:
            pass
        finally:
            self.root.after(100, self._poll_queue)

    def _handle_msg(self, msg_type, data):
        if msg_type == 'search_result':
            self._on_search_result(data)
        elif msg_type == 'search_preload':
            self._on_search_preload(data)
        elif msg_type == 'search_error':
            self._set_status(f'错误: {data}')
            messagebox.showerror('错误', data)
        elif msg_type == 'album_loaded':
            self._on_album_loaded(data)
        elif msg_type == 'rankings_result':
            self._on_rankings_result(data)
        elif msg_type == 'rankings_preload':
            self._on_rankings_preload(data)
        elif msg_type == 'login_success':
            self._on_login_success(data)
        elif msg_type == 'login_error':
            self._on_login_error(data)
        elif msg_type == 'favorites_loaded':
            self._on_favorites_loaded(data)
        elif msg_type == 'favorites_page':
            self._on_favorites_page(data)
        elif msg_type == 'dl_progress_total':
            self._dl_total = data
            self._dl_done = 0
            self.dl_progress.configure(maximum=data, value=0)
            self.dl_progress_var.set(f'0 / {data}')
            self.dl_start_btn.configure(state=tk.DISABLED)
        elif msg_type == 'dl_status':
            idx, status, detail, pid = data
            children = self.dl_tree.get_children()
            if idx is not None and idx < len(children):
                values = list(self.dl_tree.item(children[idx], 'values'))
                if len(values) >= 3:
                    values[2] = status
                    values[3] = detail
                    values[4] = '...' if status == '下载中' else (
                        'OK' if status == '已完成' else '')
                    self.dl_tree.item(children[idx], values=values)
            if status == '已完成':
                self._dl_done += 1
                self.dl_progress.configure(value=self._dl_done)
                self.dl_progress_var.set(f'{self._dl_done} / {self._dl_total}')
        elif msg_type == 'dl_done':
            self._dl_task = None
            self.dl_start_btn.configure(state=tk.NORMAL)
            if data:
                self._set_status(f'下载完成，出错: {data}')
            else:
                self._set_status(
                    f'下载完成 ({self._dl_done}/{self._dl_total})')
            self._pid_to_idx.clear()

    def _set_status(self, msg):
        self.status_var.set(msg)

    def run(self):
        self.root.mainloop()


if __name__ == '__main__':
    app = JmGUI()
    app.run()
