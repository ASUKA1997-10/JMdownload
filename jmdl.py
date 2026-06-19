"""
jm助手 - jmcomic 图形界面搜索下载工具
功能: 搜索漫画、浏览章节、下载管理
"""
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import threading
import queue
import pathlib

from jmcomic import JmOption, download_photo, JmcomicException, JmMagicConstants

_PAD_X = 5
_PAD_X_SM = 2
_PAD_Y = 5
_COMBO_WIDTH = 10

FEATURES = {
    'pdf':      None,
    'zip':      None,
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
}
ORDER_KEYS = list(ORDER_LABELS.keys())
TIME_KEYS = list(TIME_LABELS.keys())
CAT_KEYS = list(CATEGORY_LABELS.keys())


class JmGUI:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title('jm助手')
        self.root.geometry('800x700')
        self.root.minsize(700, 600)
        self.root.bind('<Control-q>', lambda e: self.root.destroy())
        self.root.protocol('WM_DELETE_WINDOW', self.root.destroy)

        self.download_dir = str(pathlib.Path.home() / 'Downloads')

        self.option = JmOption.default()
        self.option.dir_rule.base_dir = self.download_dir
        self.client = self.option.new_jm_client()

        self.order_by = JmMagicConstants.ORDER_BY_LATEST
        self.time = JmMagicConstants.TIME_ALL
        self.category = JmMagicConstants.CATEGORY_ALL

        self._search_page = 1
        self._search_items = []
        self._search_page_count = 0
        self._search_keyword = ''

        self._current_aid = None
        self._current_album = None
        self._episodes = []
        self._ep_page = 1
        self._ep_reversed = False
        self._ep_page_size = 20

        self._download_queue = []
        self._downloading = False
        self._ch_multi = False
        self._dl_multi = False

        self._result_queue = queue.Queue()

        self._init_features()
        self._build_ui()
        self._poll_queue()

    def _init_features(self):
        from jmcomic import Feature
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
                               relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.LEFT, fill=tk.X, expand=True)

        quit_btn = ttk.Button(bottom_frame, text='退出', command=self.root.destroy)
        quit_btn.pack(side=tk.RIGHT, padx=_PAD_X)

    def _build_notebook(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=_PAD_X, pady=_PAD_Y)

        self._build_search_tab()
        self._build_chapter_tab()
        self._build_download_tab()

    def _combobox(self, parent, values, default=0, width=_COMBO_WIDTH):
        cb = ttk.Combobox(parent, values=values, state='readonly', width=width)
        cb.current(default)
        return cb

    # ---------- Tab 1: 搜索 ----------
    def _build_search_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='搜索')
        tab.columnconfigure(0, weight=1)

        search_bar_frame = ttk.Frame(tab)
        search_bar_frame.grid(row=0, column=0, sticky=tk.EW, padx=_PAD_X, pady=(_PAD_Y, 0))
        search_bar_frame.columnconfigure(1, weight=1)

        ttk.Label(search_bar_frame, text='关键词:').grid(row=0, column=0, padx=_PAD_X_SM)
        self.search_entry = ttk.Entry(search_bar_frame)
        self.search_entry.grid(row=0, column=1, sticky=tk.EW, padx=_PAD_X_SM)
        self.search_entry.bind('<Return>', lambda e: self.do_search())
        ttk.Button(search_bar_frame, text='搜索', command=self.do_search).grid(row=0, column=2, padx=_PAD_X_SM)

        ttk.Separator(search_bar_frame, orient=tk.VERTICAL).grid(row=0, column=3, padx=_PAD_X, sticky=tk.NS)

        ttk.Label(search_bar_frame, text='ID:').grid(row=0, column=4, padx=_PAD_X_SM)
        self.id_entry = ttk.Entry(search_bar_frame, width=12)
        self.id_entry.grid(row=0, column=5, padx=_PAD_X_SM)
        self.id_entry.bind('<Return>', lambda e: self.do_id_lookup())
        ttk.Button(search_bar_frame, text='直查', command=self.do_id_lookup).grid(row=0, column=6, padx=_PAD_X_SM)

        filter_frame = ttk.Frame(tab)
        filter_frame.grid(row=1, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_X_SM)
        filter_frame.columnconfigure(7, weight=1)

        ttk.Label(filter_frame, text='排序:').grid(row=0, column=0, padx=_PAD_X_SM)
        self.sort_cb = self._combobox(filter_frame, list(ORDER_LABELS.values()))
        self.sort_cb.grid(row=0, column=1, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='时间:').grid(row=0, column=2, padx=_PAD_X_SM)
        self.time_cb = self._combobox(filter_frame, list(TIME_LABELS.values()))
        self.time_cb.grid(row=0, column=3, padx=_PAD_X_SM)

        ttk.Label(filter_frame, text='分类:').grid(row=0, column=4, padx=_PAD_X_SM)
        self.category_cb = self._combobox(filter_frame, list(CATEGORY_LABELS.values()))
        self.category_cb.grid(row=0, column=5, padx=_PAD_X_SM)

        ttk.Button(filter_frame, text='应用筛选', command=self._apply_filter).grid(row=0, column=6, padx=_PAD_X_SM)

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
        self.search_tree.column('title', width=400)
        self.search_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.search_tree.bind('<Double-1>', lambda e: self._on_search_double_click())

        scroll = ttk.Scrollbar(result_frame, orient=tk.VERTICAL, command=self.search_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.search_tree.configure(yscrollcommand=scroll.set)

        pager_frame = ttk.Frame(tab)
        pager_frame.grid(row=3, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.search_prev_btn = ttk.Button(pager_frame, text='上一页', command=self._search_prev)
        self.search_prev_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.search_page_var = tk.StringVar(value='第 0/0 页')
        ttk.Label(pager_frame, textvariable=self.search_page_var).pack(side=tk.LEFT, padx=10)

        self.search_next_btn = ttk.Button(pager_frame, text='下一页', command=self._search_next)
        self.search_next_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.search_total_var = tk.StringVar(value='共 0 条')
        ttk.Label(pager_frame, textvariable=self.search_total_var).pack(side=tk.LEFT, padx=10)

        ttk.Button(pager_frame, text='查看章节', command=self._on_search_double_click).pack(side=tk.RIGHT, padx=_PAD_X)

    # ---------- Tab 2: 章节 ----------
    def _build_chapter_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text='章节')
        tab.columnconfigure(0, weight=1)
        tab.rowconfigure(2, weight=1)

        self.album_info_var = tk.StringVar(value='未选择专辑')
        ttk.Label(tab, textvariable=self.album_info_var, font=('', 11, 'bold')).grid(
            row=0, column=0, sticky=tk.W, padx=_PAD_X, pady=_PAD_Y)

        chapter_toolbar = ttk.Frame(tab)
        chapter_toolbar.grid(row=1, column=0, sticky=tk.EW, padx=_PAD_X)

        ttk.Button(chapter_toolbar, text='全选', command=self._ch_select_all).pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(chapter_toolbar, text='反选', command=self._ch_invert_selection).pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.ch_multi_var = tk.BooleanVar(value=False)
        self.ch_multi_cb = ttk.Checkbutton(chapter_toolbar, text='多选模式',
                                           variable=self.ch_multi_var,
                                           command=self._ch_toggle_multi)
        self.ch_multi_cb.pack(side=tk.LEFT, padx=10)

        ttk.Button(chapter_toolbar, text='加入下载队列', command=self._ch_add_to_queue).pack(side=tk.RIGHT, padx=_PAD_X)

        chapter_list_frame = ttk.Frame(tab)
        chapter_list_frame.grid(row=2, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
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
        self.ch_tree.tag_configure('selected', background='#b3d9ff')
        self.ch_tree.tag_configure('unselected', background='')
        self.ch_tree.bind('<ButtonRelease-1>', self._ch_click_toggle)

        scroll = ttk.Scrollbar(chapter_list_frame, orient=tk.VERTICAL, command=self.ch_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.ch_tree.configure(yscrollcommand=scroll.set)

        chapter_controls = ttk.Frame(tab)
        chapter_controls.grid(row=3, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.ch_prev_btn = ttk.Button(chapter_controls, text='上页', command=self._ch_prev)
        self.ch_prev_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.ch_page_var = tk.StringVar(value='第 0/0 页')
        ttk.Label(chapter_controls, textvariable=self.ch_page_var).pack(side=tk.LEFT, padx=10)

        self.ch_next_btn = ttk.Button(chapter_controls, text='下页', command=self._ch_next)
        self.ch_next_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.ch_order_btn = ttk.Button(chapter_controls, text='倒序', command=self._ch_toggle_order)
        self.ch_order_btn.pack(side=tk.LEFT, padx=10)

    # ---------- Tab 3: 下载管理 ----------
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
        ttk.Button(toolbar_frame, text='选择目录', command=self._dl_choose_dir).pack(side=tk.LEFT, padx=_PAD_X_SM)

        dl_list_frame = ttk.Frame(tab)
        dl_list_frame.grid(row=1, column=0, sticky=tk.NSEW, padx=_PAD_X, pady=_PAD_Y)
        dl_list_frame.columnconfigure(0, weight=1)
        dl_list_frame.rowconfigure(0, weight=1)

        self.dl_tree = ttk.Treeview(dl_list_frame, columns=('album', 'chapter', 'status', 'progress'),
                                    show='headings', height=12, selectmode='none')
        self.dl_tree.heading('album', text='专辑')
        self.dl_tree.heading('chapter', text='章节')
        self.dl_tree.heading('status', text='状态')
        self.dl_tree.heading('progress', text='进度')
        self.dl_tree.column('album', width=180)
        self.dl_tree.column('chapter', width=250)
        self.dl_tree.column('status', width=80, anchor=tk.CENTER)
        self.dl_tree.column('progress', width=80, anchor=tk.CENTER)
        self.dl_tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.dl_tree.tag_configure('selected', background='#b3d9ff')
        self.dl_tree.tag_configure('unselected', background='')
        self.dl_tree.bind('<ButtonRelease-1>', self._dl_click_toggle)

        scroll = ttk.Scrollbar(dl_list_frame, orient=tk.VERTICAL, command=self.dl_tree.yview)
        scroll.grid(row=0, column=1, sticky=tk.NS)
        self.dl_tree.configure(yscrollcommand=scroll.set)

        button_frame = ttk.Frame(tab)
        button_frame.grid(row=2, column=0, sticky=tk.EW, padx=_PAD_X, pady=_PAD_Y)

        self.dl_start_btn = ttk.Button(button_frame, text='开始下载', command=self._dl_start)
        self.dl_start_btn.pack(side=tk.LEFT, padx=_PAD_X_SM)

        ttk.Button(button_frame, text='全部开始', command=self._dl_start_all).pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(button_frame, text='清除已完成', command=self._dl_clear_done).pack(side=tk.LEFT, padx=_PAD_X_SM)
        ttk.Button(button_frame, text='移除选中', command=self._dl_remove_selected).pack(side=tk.LEFT, padx=_PAD_X_SM)

        self.dl_multi_var = tk.BooleanVar(value=False)
        self.dl_multi_cb = ttk.Checkbutton(button_frame, text='多选模式',
                                           variable=self.dl_multi_var,
                                           command=self._dl_toggle_multi)
        self.dl_multi_cb.pack(side=tk.RIGHT, padx=_PAD_X_SM)

    # ========== 搜索 ==========

    def do_search(self):
        keyword = self.search_entry.get().strip()
        if not keyword:
            return
        self._search_keyword = keyword
        self._search_page = 1
        self._set_status('搜索中...')
        self.search_tree.delete(*self.search_tree.get_children())
        self._search_items.clear()
        order_val = ORDER_KEYS[self.sort_cb.current()]
        time_val = TIME_KEYS[self.time_cb.current()]
        cat_val = CAT_KEYS[self.category_cb.current()]
        t = threading.Thread(
            target=self._search_worker,
            args=(keyword, 1, order_val, time_val, cat_val),
            daemon=True,
        )
        t.start()

    def _search_worker(self, keyword, page, order_val, time_val, cat_val):
        try:
            result = self.client.search_site(
                search_query=keyword,
                page=page,
                order_by=order_val,
                time=time_val,
                category=cat_val,
            )
            items = list(result.iter_id_title())
            self._result_queue.put(('search_result', {
                'items': items,
                'page': page,
                'page_count': result.page_count,
                'total': result.total,
            }))
        except Exception as e:
            self._result_queue.put(('search_error', str(e)))

    def _on_search_result(self, data):
        self._search_items = data['items']
        self._search_page = data['page']
        self._search_page_count = data['page_count']
        total = data['total']

        self.search_tree.delete(*self.search_tree.get_children())
        for i, (aid, title) in enumerate(data['items'], 1):
            self.search_tree.insert('', tk.END, values=(i, aid, title))

        self.search_page_var.set(f'第 {self._search_page}/{self._search_page_count} 页')
        self.search_total_var.set(f'共 {total} 条')
        self._update_search_nav()
        self._set_status(f'搜索完成，共 {total} 条结果')

    def _update_search_nav(self):
        self.search_prev_btn.configure(state=tk.NORMAL if self._search_page > 1 else tk.DISABLED)
        self.search_next_btn.configure(
            state=tk.NORMAL if self._search_page < self._search_page_count else tk.DISABLED)

    def _search_prev(self):
        if not self._search_keyword or self._search_page <= 1:
            return
        self._search_page -= 1
        self._set_status(f'搜索中 (第{self._search_page}页)...')
        self.search_tree.delete(*self.search_tree.get_children())
        order_val = ORDER_KEYS[self.sort_cb.current()]
        time_val = TIME_KEYS[self.time_cb.current()]
        cat_val = CAT_KEYS[self.category_cb.current()]
        t = threading.Thread(
            target=self._search_worker,
            args=(self._search_keyword, self._search_page, order_val, time_val, cat_val),
            daemon=True,
        )
        t.start()

    def _search_next(self):
        if not self._search_keyword or self._search_page >= self._search_page_count:
            return
        self._search_page += 1
        self._set_status(f'搜索中 (第{self._search_page}页)...')
        self.search_tree.delete(*self.search_tree.get_children())
        order_val = ORDER_KEYS[self.sort_cb.current()]
        time_val = TIME_KEYS[self.time_cb.current()]
        cat_val = CAT_KEYS[self.category_cb.current()]
        t = threading.Thread(
            target=self._search_worker,
            args=(self._search_keyword, self._search_page, order_val, time_val, cat_val),
            daemon=True,
        )
        t.start()

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
        t = threading.Thread(target=self._id_lookup_worker, args=(aid,), daemon=True)
        t.start()

    def _id_lookup_worker(self, aid):
        try:
            album = self.client.get_album_detail(aid)
            self._result_queue.put(('album_loaded', album))
        except Exception as e:
            self._result_queue.put(('search_error', f'查询失败 JM{aid}: {e}'))

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
        t = threading.Thread(target=self._search_lookup_worker, args=(aid,), daemon=True)
        t.start()

    def _search_lookup_worker(self, aid):
        try:
            album = self.client.get_album_detail(aid)
            self._result_queue.put(('album_loaded', album))
        except Exception as e:
            self._result_queue.put(('search_error', f'获取专辑失败: {e}'))

    def _load_album(self, album):
        self._current_aid = album.id
        self._current_album = album
        self._episodes = album.episode_list
        self._ep_page = 1
        self._ep_reversed = False
        self.ch_order_btn.configure(text='倒序')
        title = album.name or album.title
        self.album_info_var.set(f'JM{self._current_aid} - {title}')
        self._refresh_ch_page()
        self.notebook.select(1)

    # ========== 章节 ==========

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
        self.ch_prev_btn.configure(state=tk.NORMAL if self._ep_page > 1 else tk.DISABLED)
        self.ch_next_btn.configure(state=tk.NORMAL if self._ep_page < page_count else tk.DISABLED)

        self.ch_tree.delete(*self.ch_tree.get_children())
        for i in range(start, end):
            ep = self._get_ep(i)
            pid, pidx, ptitle = ep[0], ep[1], ep[2]
            label = ptitle if ptitle else f'章节{pidx}'
            self.ch_tree.insert('', tk.END, values=(i + 1, label, pid), tags=('unselected',))

    def _ch_prev(self):
        if self._ep_page > 1:
            self._ep_page -= 1
            self._refresh_ch_page()

    def _ch_next(self):
        page_count = max(1, (self._ep_count() + self._ep_page_size - 1) // self._ep_page_size)
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
            self.ch_tree.item(item, tags=('unselected',) if 'selected' in tags else ('selected',))

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
                self._download_queue.append((self._current_aid, title, pid, plabel))
                added += 1
        if added > 0:
            self._refresh_dl_tree()
            self._set_status(f'已添加 {added} 个章节到下载队列')
            self.notebook.select(2)
        else:
            messagebox.showinfo('提示', '请先在章节列表中勾选要下载的章节')

    # ========== 下载管理 ==========

    def _refresh_dl_tree(self):
        self.dl_tree.delete(*self.dl_tree.get_children())
        for _, title, _, plabel in self._download_queue:
            self.dl_tree.insert('', tk.END, values=(title, plabel, '等待中', ''),
                                tags=('unselected',))

    def _dl_choose_dir(self):
        chosen = filedialog.askdirectory(initialdir=self.download_dir, title='选择下载目录')
        if chosen:
            self.download_dir = chosen
            self.option.dir_rule.base_dir = chosen
            self.dir_var.set(chosen)
            self._set_status(f'下载目录已切换: {chosen}')

    def _dl_start(self):
        if self._downloading:
            return
        indices = self._dl_get_selected_indices()
        if not indices:
            messagebox.showinfo('提示', '请先在下载列表中选择要下载的项目')
            return
        self._downloading = True
        self.dl_start_btn.configure(state=tk.DISABLED)
        self._set_status('下载中...')
        fmt_key = list(FORMAT_LABELS.keys())[self.fmt_cb.current()]
        t = threading.Thread(target=self._download_worker,
                             args=(indices, fmt_key), daemon=True)
        t.start()

    def _dl_start_all(self):
        if self._downloading or not self._download_queue:
            return
        self._downloading = True
        self.dl_start_btn.configure(state=tk.DISABLED)
        self._set_status('下载中...')
        all_indices = list(range(len(self._download_queue)))
        fmt_key = list(FORMAT_LABELS.keys())[self.fmt_cb.current()]
        t = threading.Thread(target=self._download_worker,
                             args=(all_indices, fmt_key), daemon=True)
        t.start()

    def _download_worker(self, indices, fmt_key):
        try:
            for idx in sorted(indices):
                if idx >= len(self._download_queue):
                    continue
                aid, title, pid, plabel = self._download_queue[idx]
                self._result_queue.put(('dl_status', (idx, '下载中')))
                try:
                    download_photo(int(pid), self.option, extra=FEATURES[fmt_key])
                    self._result_queue.put(('dl_status', (idx, '已完成')))
                except JmcomicException as e:
                    self._result_queue.put(('dl_status', (idx, f'失败: {e}')))
            self._result_queue.put(('dl_done', None))
        except Exception as e:
            self._result_queue.put(('dl_done', str(e)))

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

    # ========== 线程通信 ==========

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
        elif msg_type == 'search_error':
            self._set_status(f'错误: {data}')
            messagebox.showerror('错误', data)
        elif msg_type == 'album_loaded':
            self._on_album_loaded(data)
        elif msg_type == 'dl_status':
            idx, status = data
            children = self.dl_tree.get_children()
            if idx < len(children):
                values = list(self.dl_tree.item(children[idx], 'values'))
                if len(values) >= 3:
                    values[2] = status
                    values[3] = '...' if status == '下载中' else ('100%' if status == '已完成' else '')
                    self.dl_tree.item(children[idx], values=values)
        elif msg_type == 'dl_done':
            self._downloading = False
            self.dl_start_btn.configure(state=tk.NORMAL)
            if data:
                self._set_status(f'下载出错: {data}')
            else:
                self._set_status('下载完成')

    def _set_status(self, msg):
        self.status_var.set(msg)

    def run(self):
        self.root.mainloop()


if __name__ == '__main__':
    app = JmGUI()
    app.run()
