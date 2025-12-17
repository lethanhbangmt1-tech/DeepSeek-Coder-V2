#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Container Packing GUI - Advanced Improved Version with Gap-Filling Algorithm
Enhanced DXF Export with Rotation Marking and Top View
Version 3.0 - Two-Tab Interface with Improved Layout
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import random
import csv
import math
from collections import defaultdict, Counter
import heapq
import time
from datetime import datetime
import os
import dim_module

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.patches import Rectangle
from matplotlib.backends.backend_pdf import PdfPages

try:
    import pandas as pd
    PANDAS_AVAILABLE = True
except ImportError:
    PANDAS_AVAILABLE = False

try:
    import ezdxf
    from ezdxf import bbox
    from ezdxf.enums import TextEntityAlignment
    DXF_AVAILABLE = True
except ImportError:
    DXF_AVAILABLE = False

# ---------------- MAIN APPLICATION ----------------
class ContainerAppAdvanced:
    def clear_drag_selection(self, event=None):
        self.dragged_item = None
        self.drag_source = None
        self.selected_source_index = None
        self.selected_item_indices = []
        try: self.draw_source_views()
        except: pass
        try: self.draw_move_view_3d()
        except: pass
        try: self.update_selection_info_3d()
        except: pass
        if hasattr(self,'transfer_status_label'):
            self.transfer_status_label.config(text='Đã hủy chọn item', foreground='blue')
    def clear_selected_item(self):
        # Hủy chọn item đích & nguồn (nút 🚫 BỎ CHỌN)
        self.selected_item_indices = []
        self.selected_source_index = None
        self.dragged_item = None
        self.drag_source = None

        # Xóa highlight nếu tồn tại
        if hasattr(self, "highlight_patch") and self.highlight_patch:
            try:
                self.highlight_patch.remove()
            except:
                pass
            self.highlight_patch = None

        # Reset label trạng thái
        if hasattr(self, "transfer_status_label"):
            self.transfer_status_label.config(
                text="Đã bỏ chọn item",
                foreground="gray"
            )

        # Vẽ lại các view
        try:
            if hasattr(self, "draw_move_view_3d"):
                self.draw_move_view_3d()
        except:
            pass

        try:
            if hasattr(self, "draw_source_views"):
                self.draw_source_views()
        except:
            pass
    def _forward_section_dim_event(self, event, ax):
        if not getattr(self, "dim_mode", False):
            return
        if event.inaxes != ax:
            return
        dim_module._on_mouse_click(self, event)

    # =============================================================
    # ZOOM / PAN for matplotlib axes (scroll to zoom, right mouse drag to pan, double-click to reset)
    # =============================================================
    def enable_zoom_pan(self, canvas, ax):
        # Lưu lại giới hạn ban đầu để reset
        if not hasattr(self, '_zoom_original_limits'):
            self._zoom_original_limits = {}
        key = id(ax)
        self._zoom_original_limits[key] = (ax.get_xlim(), ax.get_ylim())

        def on_scroll(event):
            if event.inaxes != ax:
                return
            base_scale = 1.2
            cur_xlim = ax.get_xlim()
            cur_ylim = ax.get_ylim()
            xdata = event.xdata
            ydata = event.ydata
            if xdata is None or ydata is None:
                return

            # zoom in: button == 'up', zoom out: 'down'
            scale = base_scale if event.button == 'up' else 1 / base_scale

            new_width = (cur_xlim[1] - cur_xlim[0]) * scale
            new_height = (cur_ylim[1] - cur_ylim[0]) * scale

            relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0] or 1)
            rely = (cur_ylim[1] - ydata) / (cur_ylim[1] - cur_ylim[0] or 1)

            ax.set_xlim([xdata - new_width * (1 - relx), xdata + new_width * relx])
            ax.set_ylim([ydata - new_height * (1 - rely), ydata + new_height * rely])
            canvas.draw_idle()

        self._pan_start = None

        def on_press(event):
            if event.inaxes != ax:
                return
            # Chuột phải để pan
            if event.button == 3:
                self._pan_start = (event.xdata, event.ydata)

        def on_release(event):
            self._pan_start = None

        def on_move(event):
            if self._pan_start is None or event.inaxes != ax:
                return
            dx = self._pan_start[0] - event.xdata
            dy = self._pan_start[1] - event.ydata

            xlim = ax.get_xlim()
            ylim = ax.get_ylim()
            ax.set_xlim(xlim[0] + dx, xlim[1] + dx)
            ax.set_ylim(ylim[0] + dy, ylim[1] + dy)
            canvas.draw_idle()

        def on_double_click(event):
            if event.inaxes != ax or not event.dblclick:
                return
            # Reset về giới hạn ban đầu
            lims = self._zoom_original_limits.get(key)
            if lims:
                ax.set_xlim(*lims[0])
                ax.set_ylim(*lims[1])
                canvas.draw_idle()

        canvas.mpl_connect("scroll_event", on_scroll)
        canvas.mpl_connect("button_press_event", on_press)
        canvas.mpl_connect("button_release_event", on_release)
        canvas.mpl_connect("motion_notify_event", on_move)
        canvas.mpl_connect("button_press_event", on_double_click)

    def __init__(self, root):
        self.root = root
        self.root.title("CONTAINER PACKING ADVANCED - VERSION 3.0")

        # LOGO
        logo_frame = tk.Frame(self.root, bg="#EEEEEE")
        logo_frame.pack(fill="x", pady=0.5)

        logo_inner = tk.Frame(logo_frame, bg="#EEEEEE")
        logo_inner.pack(pady=0.5)

        lbl_pergolux = tk.Label(
            logo_inner,
            text="NGOC DIEP - PERGOLUX",
            font=("Segoe UI", 18, "bold"),
            fg="#0F7B3A",
            bg="#EEEEEE"
        )
        lbl_pergolux.pack(side="left", padx=5)

        self.root.geometry("1600x900")
        self.root.minsize(1200, 700)

        # Container dimensions (default: 40ft HC)
        self.container_length = tk.IntVar(value=12000)
        self.container_width = tk.IntVar(value=2340)
        self.container_height = tk.IntVar(value=2610)

        self.result = None
        self.rotation_analysis = None
        
        # Layer movement state
        self.selected_item_indices = []
        self.ctrl_pressed = False
        self.undo_stack = []
        self.redo_stack = []
        self.max_undo_steps = 20

        # Drag-drop state
        self.dragged_item = None
        self.drag_source = None
        self.selected_source_index = None
        
        # Stacking strategy
        self.stack_strategy = tk.StringVar(value="2d_packing")  # 2d_packing: tk
        
        # Thêm biến cho tolerance chiều cao
        self.height_tolerance_var = tk.IntVar(value=10)  # Giá trị mặc định 10mm
        
        self.build_layout()

    # --- GUI LAYOUT ---
    def build_layout(self):
        # Tạo Notebook chính với 2 Tab
        main_notebook = ttk.Notebook(self.root)
        main_notebook.pack(fill="both", expand=True, padx=10, pady=10)
        
        # ========== TAB 1: CÁC THÔNG SỐ ĐẦU VÀO, CHI TIẾT SẾP CẤU KIỆN ==========
        tab1 = ttk.Frame(main_notebook)
        main_notebook.add(tab1, text="1. THÔNG SỐ ĐẦU VÀO & KẾT QUẢ")
        
        tab1_frame = ttk.Frame(tab1)
        tab1_frame.pack(fill="both", expand=True, padx=5, pady=5)
        
        # PanedWindow cho Tab 1 (giữ layout cũ)
        paned_window_tab1 = ttk.PanedWindow(tab1_frame, orient=tk.HORIZONTAL)
        paned_window_tab1.pack(fill="both", expand=True)
        
        left_frame_tab1 = ttk.Frame(paned_window_tab1, width=400)
        mid_frame_tab1 = ttk.Frame(paned_window_tab1, width=450)
        right_frame_tab1 = ttk.Frame(paned_window_tab1)
        
        paned_window_tab1.add(left_frame_tab1, weight=0)
        paned_window_tab1.add(mid_frame_tab1, weight=1)
        paned_window_tab1.add(right_frame_tab1, weight=2)
        
        self.build_left(left_frame_tab1)
        self.build_middle(mid_frame_tab1)
        self.build_right_tab1(right_frame_tab1)
        
        # ========== TAB 2: MẶT CẮT & MẶT BẰNG FULL MÀN HÌNH ==========
        tab2 = ttk.Frame(main_notebook)
        main_notebook.add(tab2, text="2. MẶT CẮT & MẶT BẰNG")
        self.build_tab2_fullscreen(tab2)

        # ===== KHÓA TAB 2 DÙNG CHUNG MẬT KHẨU =====
        self._tab2_unlocked = False

        def on_tab_change(event):
            notebook = event.widget
            selected_index = notebook.index("current")

            # TAB 2 có index = 1
            if selected_index == 1 and not self._tab2_unlocked:
                ok = self.check_password(
                    title="Authentication",
                    message="Đang phát triển"
                )

                if ok:
                    self._tab2_unlocked = True
                else:
                    notebook.select(0)   # Quay về Tab 1 nếu sai

        # ===== CHẶN CLICK TAB 2 TRƯỚC KHI HIỂN THỊ =====
        self._tab2_unlocked = False

        def on_tab_click(event):
            notebook = event.widget

            # Lấy index của tab đúng vị trí click chuột
            try:
                tab_index = notebook.index(f"@{event.x},{event.y}")
            except:
                return

            # Nếu click TAB 2 mà chưa mở khóa
            if tab_index == 1 and not self._tab2_unlocked:
                ok = self.check_password(
                    title="Authentication",
                    message="Đang phát triển chức năng này:"
                )

                if ok:
                    self._tab2_unlocked = True
                    notebook.select(1)   # Cho phép chuyển sang Tab 2
                else:
                    notebook.select(0)   # Giữ ở Tab 1

                return "break"   # CHẶN KHÔNG CHO ĐỔI TAB

        # Bắt click chuột vào tab (trước khi Notebook xử lý đổi tab)
        main_notebook.bind("<ButtonPress-1>", on_tab_click, True)


    # --- LEFT PANEL (TAB 1) ---
    def build_left(self, frame):
        ttk.Label(frame, text="1. THÔNG SỐ ĐẦU VÀO", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=2)

        cf = ttk.LabelFrame(frame, text="Kích thước Container (mm)")
        cf.pack(fill="x", pady=2)
        self.add_labeled_entry(cf, "Dài (L):", self.container_length)
        self.add_labeled_entry(cf, "Rộng (W):", self.container_width)
        self.add_labeled_entry(cf, "Cao (H):", self.container_height)

        adv_frame = ttk.LabelFrame(frame, text="Tùy chọn nâng cao")
        adv_frame.pack(fill="x", pady=2)
        
        self.allow_rotation = tk.BooleanVar(value=True)
        self.use_maxrect = tk.BooleanVar(value=True)
        self.group_similar = tk.BooleanVar(value=True)
        self.pack_density = tk.BooleanVar(value=True)
        self.multi_strategy = tk.BooleanVar(value=True)
        self.allow_stacking_in_layer = tk.BooleanVar(value=True)
        self.allow_height_tolerance = tk.BooleanVar(value=True)  # Thêm tùy chọn mới
        
        ttk.Checkbutton(adv_frame, text="Cho phép hoán đổi Y-Z", variable=self.allow_rotation).pack(anchor="w")
        ttk.Checkbutton(adv_frame, text="Sử dụng G-F", variable=self.use_maxrect).pack(anchor="w")
        ttk.Checkbutton(adv_frame, text="Gom nhóm tương tự", variable=self.group_similar).pack(anchor="w")
        ttk.Checkbutton(adv_frame, text="Tối ưu mật độ xếp", variable=self.pack_density).pack(anchor="w")
        ttk.Checkbutton(adv_frame, text="So sánh nhiều chiến lược", variable=self.multi_strategy).pack(anchor="w")
        ttk.Checkbutton(adv_frame, text="Cho chồng item thấp cùng layer", variable=self.allow_stacking_in_layer).pack(anchor="w")
        
        # Thêm frame cho tolerance chiều cao
        tolerance_frame = ttk.Frame(adv_frame)
        tolerance_frame.pack(fill="x", pady=2, anchor="w")
        
        self.allow_height_tolerance = tk.BooleanVar(value=True)
        tolerance_check = ttk.Checkbutton(tolerance_frame, text="Ưu tiên item chênh cao ≤", variable=self.allow_height_tolerance)
        tolerance_check.pack(side="left")
        
        # Entry cho giá trị tolerance
        tolerance_entry = ttk.Entry(tolerance_frame, textvariable=self.height_tolerance_var, width=5)
        tolerance_entry.pack(side="left", padx=2)
        ttk.Label(tolerance_frame, text="mm cùng layer").pack(side="left")

        # DXF export debug log toggle
        self.dxf_debug_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(adv_frame, text="Ghi log DXF khi xuất (debug)", variable=self.dxf_debug_var).pack(anchor="w")
        
        # Stacking strategy selection
        stack_frame = ttk.Frame(adv_frame)
        stack_frame.pack(fill="x", pady=2)
        
        ttk.Label(stack_frame, text="Chiến lược chồng:").pack(side="left", padx=2)
        ttk.Combobox(stack_frame, textvariable=self.stack_strategy,
                     values=["2d_packing", "same_spot", "separate"],
                     state="readonly", width=15).pack(side="left", padx=2)
        tk.Label(stack_frame, text="(-)", font=("Arial", 8, "italic"), fg="blue").pack(side="left", padx=2)

        self.setup_paste_area(frame)

        lf = ttk.LabelFrame(frame, text="Danh sách hàng (L W H Q ID Rotate)")
        lf.pack(fill="both", expand=True, pady=2)

        self.data_tree = ttk.Treeview(lf, columns=("L", "W", "H", "Q", "No.ID", "Rotate"), show="headings", height=15)
        cols = {"L": 60, "W": 60, "H": 60, "Q": 50, "No.ID": 80, "Rotate": 60}
        for c, w in cols.items():
            self.data_tree.heading(c, text=c)
            self.data_tree.column(c, width=w, anchor="center")
        # ✅ GỌI SAU KHI TẠO TREEVIEW + SET CỘT
        self.enable_treeview_edit(self.data_tree)

        scroll = ttk.Scrollbar(lf, orient="vertical", command=self.data_tree.yview)
        scroll.pack(side="right", fill="y")
        self.data_tree.configure(yscrollcommand=scroll.set)
        self.data_tree.pack(side="left", fill="both", expand=True)

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x", pady=2)
        ttk.Button(btn_frame, text="Load Mẫu", command=self.load_sample).grid(row=0, column=0, padx=2, sticky="ew")
        ttk.Button(btn_frame, text="Nhập Excel", command=self.import_excel).grid(row=0, column=1, padx=2, sticky="ew")
        ttk.Button(btn_frame, text="Thêm hàng", command=self.add_row_dialog).grid(row=0, column=2, padx=2, sticky="ew")
        ttk.Button(btn_frame, text="Xóa dòng", command=self.delete_selected).grid(row=1, column=0, padx=2, sticky="ew", pady=2)
        ttk.Button(btn_frame, text="Xóa hết", command=lambda: self.data_tree.delete(*self.data_tree.get_children())).grid(row=1, column=1, padx=2, sticky="ew", pady=2)
        
        btn_frame.columnconfigure(0, weight=1)
        btn_frame.columnconfigure(1, weight=1)
        btn_frame.columnconfigure(2, weight=1)

        tk.Button(frame, text="TÍNH TOÁN XẾP KIỆN", command=self.run_advanced_optimization,
                  bg="green", fg="white", font=("Arial", 12, "bold"),
                  relief="raised", bd=3).pack(fill="x", pady=10, ipady=10)

    def add_labeled_entry(self, parent, label, var):
        fr = ttk.Frame(parent)
        fr.pack(fill="x", pady=2)
        ttk.Label(fr, text=label).pack(side="left", padx=2)
        ttk.Entry(fr, textvariable=var, width=7).pack(side="right", padx=2)

    def setup_paste_area(self, frame):
        box = ttk.LabelFrame(frame, text="Dán Excel (Ctrl+V)")
        box.pack(fill="x", pady=2)
        self.preview_tree = ttk.Treeview(box, columns=("L", "W", "H", "Q", "No.ID", "Rotate"), show="headings", height=3)
        for c in ("L", "W", "H", "Q", "No.ID", "Rotate"):
            self.preview_tree.heading(c, text=c)
            self.preview_tree.column(c, width=50, anchor="center")
        self.preview_tree.pack(fill="x", padx=2)
        
        self.hidden_paste = tk.Text(box, height=1, width=1)
        self.hidden_paste.place(x=-999, y=-999)
        self.root.bind_all("<Control-v>", self.handle_paste)
        ttk.Button(box, text="▼ Thêm vào danh sách", command=self.commit_preview).pack(fill="x", padx=2, pady=2)

    def handle_paste(self, event=None):
        try:
            self.hidden_paste.delete("1.0", "end")
            self.hidden_paste.event_generate("<<Paste>>")
            raw = self.hidden_paste.get("1.0", "end").strip()
            if not raw:
                return
            self.preview_tree.delete(*self.preview_tree.get_children())
            for ln in raw.splitlines():
                parts = ln.replace("\t", " ").replace(",", " ").split()
                if len(parts) >= 4:
                    try:
                        L, W, H, Q = map(int, parts[:4])
                        no_id = parts[4] if len(parts) >= 5 else f"Item{len(self.preview_tree.get_children())+1}"
                        rotate = parts[5] if len(parts) >= 6 else "1"
                        self.preview_tree.insert("", "end", values=(L, W, H, Q, no_id, rotate))
                    except ValueError:
                        pass
        except Exception:
            pass

    def commit_preview(self):
        rows = self.preview_tree.get_children()
        if rows:
            for r in rows:
                self.data_tree.insert("", "end", values=self.preview_tree.item(r, "values"))
            self.preview_tree.delete(*rows)
            messagebox.showinfo("Info", "Đã thêm dữ liệu.")


    # =====================================================
    # EXCEL-LIKE EDIT FOR TREEVIEW (DOUBLE CLICK TO EDIT)
    # =====================================================
    def enable_treeview_edit(self, tree):
        tree.bind("<Double-1>", self._on_treeview_double_click)

    def _on_treeview_double_click(self, event):
        tree = event.widget

        region = tree.identify("region", event.x, event.y)
        if region != "cell":
            return

        row_id = tree.identify_row(event.y)
        column = tree.identify_column(event.x)

        if not row_id or not column:
            return

        x, y, width, height = tree.bbox(row_id, column)
        col_index = int(column.replace("#", "")) - 1

        values = list(tree.item(row_id, "values"))
        old_value = values[col_index]

        entry = ttk.Entry(tree)
        entry.place(x=x, y=y, width=width, height=height)
        entry.insert(0, old_value)
        entry.focus_set()

        def save_edit(event=None):
            values[col_index] = entry.get()
            tree.item(row_id, values=values)
            entry.destroy()

        entry.bind("<Return>", save_edit)
        entry.bind("<FocusOut>", save_edit)
        entry.bind("<Escape>", lambda e: entry.destroy())
   
    # --- MIDDLE PANEL (TAB 1) ---
    def build_middle(self, frame):
        ttk.Label(frame, text="2. KẾT QUẢ CHI TIẾT", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=2)
        
        box = ttk.LabelFrame(frame, text="Danh sách kiện theo từng lớp")
        box.pack(fill="both", expand=True, pady=2)
        
        self.result_text = tk.Text(box, width=40, height=30, font=("Consolas", 10))
        self.result_text.pack(fill="both", expand=True, padx=2, pady=2)
        
        self.result_text.tag_config("CONT", foreground="blue", font=("Consolas", 11, "bold"))
        self.result_text.tag_config("LAYER", foreground="#8B4500", font=("Consolas", 10, "bold"))
        self.result_text.tag_config("ITEM", foreground="black")
        self.result_text.tag_config("WARN", foreground="red")
        self.result_text.tag_config("BEST", foreground="green", font=("Consolas", 11, "bold"))
        self.result_text.tag_config("ROTATE", foreground="purple", font=("Consolas", 10, "bold"))

        btns = ttk.Frame(frame)
        btns.pack(fill="x")
        ttk.Button(btns, text="Excel Export", command=self.export_excel).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(btns, text="Section DXF", command=self.export_dxf).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(btns, text="DXF Layers", command=self.export_dxf_layers).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(btns, text="Reorder layers", command=self.reorder_layers).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(btns, text="Move Item 3D", command=self.move_items_3d_with_password).pack(side="left", fill="x", expand=True, padx=2)

    # ===== PASSWORD DÙNG CHUNG CHO MOVE ITEM + TAB 2 =====
    def check_password(self, title="XÁC THỰC", message="Nhập mật khẩu:"):
        import tkinter.simpledialog as simpledialog
        import tkinter.messagebox as messagebox

        PASSWORD = ".."   # ✅ ĐỔI MẬT KHẨU TẠI ĐÂY

        user_pass = simpledialog.askstring(
            title,
            message,
            show="*"
        )

        if user_pass is None:
            return False

        if user_pass == PASSWORD:
            return True
        else:
            messagebox.showerror("Error", "Đang phát triển chức năng này!")
            return False

    def move_items_3d_with_password(self):
        if self.check_password(
            title="Authentication",
            message="Đang phát triển chức năng này:"
        ):
            self.move_items_3d()


    # --- RIGHT PANEL (TAB 1) ---
    def build_right_tab1(self, frame):
        ttk.Label(frame, text="3. MÔ HÌNH 2D", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=2)
        tk.Label(frame, text="Written by Mr. Bang", fg="#666666", font=("Segoe UI", 10)).place(relx=0.95, y=5, anchor="ne")

        tabs = ttk.Notebook(frame)
        tabs.pack(fill="both", expand=True)
        
        preview_tab = ttk.Frame(tabs)
        tabs.add(preview_tab, text="Xem Nhanh")
        
        full_view_tab = ttk.Frame(tabs)
        tabs.add(full_view_tab, text="Mô Hình 2D Full")
        
        self.build_preview_tab(preview_tab)
        self.build_full_view_tab(full_view_tab)

    def build_preview_tab(self, frame):
        cross_section_frame = ttk.LabelFrame(frame, text="Mặt cắt ngang tại các vị trí 2.0m, 5.0m, 8.0m, 11.0m")
        cross_section_frame.pack(fill="x", pady=2)
        
        self.fig_cross, self.ax_cross = plt.subplots(1, 4, figsize=(12, 3))
        self.fig_cross.tight_layout(pad=3.0)
        self.cv_cross = FigureCanvasTkAgg(self.fig_cross, master=cross_section_frame)
        self.cv_cross.get_tk_widget().pack(fill="x", expand=True)
        
        cross_btn_frame = ttk.Frame(cross_section_frame)
        cross_btn_frame.pack(fill="x", pady=2)
        ttk.Button(cross_btn_frame, text="Xuất PDF Mặt Cắt Ngang", 
                  command=self.export_cross_sections_pdf).pack(side="left", padx=2)
        
        ctrl = ttk.LabelFrame(frame, text="Chọn góc nhìn")
        ctrl.pack(fill="x", pady=2)
        
        ttk.Label(ctrl, text="Xe:").pack(side="left", padx=2)
        self.cb_container = ttk.Combobox(ctrl, state="readonly", width=7)
        self.cb_container.pack(side="left", padx=2)
        self.cb_container.bind("<<ComboboxSelected>>", self.on_cont_change)
        
        ttk.Label(ctrl, text="Lớp:").pack(side="left", padx=2)
        self.cb_layer = ttk.Combobox(ctrl, state="readonly", width=12)
        self.cb_layer.pack(side="left", padx=2)
        self.cb_layer.bind("<<ComboboxSelected>>", self.on_layer_change)

        tabs = ttk.Notebook(frame)
        tabs.pack(fill="both", expand=True)
        
        t1 = ttk.Frame(tabs)
        t2 = ttk.Frame(tabs)
        tabs.add(t1, text="Mặt Bằng (Top)")
        tabs.add(t2, text="Mặt Đứng (Side)")
        
        self.fig_top, self.ax_top = plt.subplots(figsize=(12, 7))
        self.cv_top = FigureCanvasTkAgg(self.fig_top, master=t1)
        self.cv_top.get_tk_widget().pack(fill="both", expand=True)
        
        self.fig_el, self.ax_el = plt.subplots(figsize=(12, 7))
        self.cv_el = FigureCanvasTkAgg(self.fig_el, master=t2)
        self.cv_el.get_tk_widget().pack(fill="both", expand=True)

    def build_full_view_tab(self, frame):
        control_frame = ttk.Frame(frame)
        control_frame.pack(fill="x", pady=2, padx=2)
        
        ttk.Label(control_frame, text="Chọn xe:").pack(side="left", padx=2)
        self.full_cb_container = ttk.Combobox(control_frame, state="readonly", width=15)
        self.full_cb_container.pack(side="left", padx=2)
        self.full_cb_container.bind("<<ComboboxSelected>>", self.on_full_cont_change)
        
        ttk.Label(control_frame, text="Chọn lớp:").pack(side="left", padx=2)
        self.full_cb_layer = ttk.Combobox(control_frame, state="readonly", width=15)
        self.full_cb_layer.pack(side="left", padx=2)
        self.full_cb_layer.bind("<<ComboboxSelected>>", self.on_full_layer_change)
        
        ttk.Label(control_frame, text="Loại hiển thị:").pack(side="left", padx=2)
        self.full_cb_view = ttk.Combobox(control_frame, state="readonly", width=15, 
                                       values=["Mặt Bằng (Top)", "Mặt Đứng (Side)"])
        self.full_cb_view.pack(side="left", padx=2)
        self.full_cb_view.set("Mặt Bằng (Top)")
        self.full_cb_view.bind("<<ComboboxSelected>>", self.on_full_view_change)
        
        self.full_export_btn = ttk.Button(control_frame, text="Xuất PDF Layer Hiện Tại", 
                                        command=self.export_full_pdf)
        self.full_export_btn.pack(side="left", padx=10)
        
        self.full_export_all_btn = ttk.Button(control_frame, text="Xuất PDF Tất Cả Layers", 
                                            command=self.export_all_layers_pdf)
        self.full_export_all_btn.pack(side="left", padx=2)

        display_frame = ttk.Frame(frame)
        display_frame.pack(fill="both", expand=True, padx=2, pady=2)
        
        self.full_fig, self.full_ax = plt.subplots(figsize=(12, 8))
        self.full_canvas = FigureCanvasTkAgg(self.full_fig, master=display_frame)
        self.full_canvas.get_tk_widget().pack(fill="both", expand=True)

    # ========== TAB 2: MẶT CẮT & MẶT BẰNG FULL MÀN HÌNH ==========
    def build_tab2_fullscreen(self, frame):
        """Xây dựng Tab 2 với 4 mặt cắt trên và Topview dưới chiếm full màn hình"""
        # PanedWindow để chia đôi màn hình
        main_paned = ttk.PanedWindow(frame, orient=tk.VERTICAL)
        main_paned.pack(fill="both", expand=True, padx=5, pady=5)
        
        # ===== PHẦN TRÊN: 4 MẶT CẮT =====
        top_section_frame = ttk.LabelFrame(main_paned, text="4 MẶT CẮT NGANG TẠI 2.0m, 5.0m, 8.0m, 11.0m")
        main_paned.add(top_section_frame, weight=3)
        
        # Khung điều khiển cho phần mặt cắt
        cross_control_frame = ttk.Frame(top_section_frame)
        cross_control_frame.pack(fill="x", padx=5, pady=5)
        
        ttk.Label(cross_control_frame, text="Chọn xe:").pack(side="left", padx=2)
        self.tab2_cross_container = ttk.Combobox(cross_control_frame, state="readonly", width=15)
        self.tab2_cross_container.pack(side="left", padx=2)
        self.tab2_cross_container.bind("<<ComboboxSelected>>", self.on_tab2_cross_container_change)
        
        ttk.Button(cross_control_frame, text="Xuất PDF Mặt Cắt", 
                  command=self.export_cross_sections_pdf).pack(side="right", padx=5)
        ttk.Button(cross_control_frame, text="📏 DIM X,Y",
                  command=lambda: dim_module.enable_dim(self)).pack(side="right", padx=5)

        ttk.Button(cross_control_frame, text="❌ TẮT DIM",
                  command=lambda: dim_module.disable_dim(self)).pack(side="right", padx=5)

        
        # Tạo 4 axes cho mặt cắt
        self.tab2_fig_cross, self.tab2_ax_cross = plt.subplots(1, 4, figsize=(20, 8))
        self.section_axes = list(self.tab2_ax_cross)
        self.tab2_fig_cross.tight_layout(pad=3.0)
        self.tab2_cv_cross = FigureCanvasTkAgg(self.tab2_fig_cross, master=top_section_frame)
        self.tab2_cv_cross.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=5)
        # GẮN DIM EVENT CHO 4 MẶT CẮT
        for ax in self.section_axes:
            ax.figure.canvas.mpl_connect(
                "button_press_event",
                lambda e, ax=ax: self._forward_section_dim_event(e, ax)
            )

        
        # ===== PHẦN DƯỚI: TOPVIEW =====
        bottom_section_frame = ttk.LabelFrame(main_paned, text="MẶT BẰNG (TOP VIEW)")
        main_paned.add(bottom_section_frame, weight=1)
        
        # Khung điều khiển cho Topview
        topview_control_frame = ttk.Frame(bottom_section_frame)
        topview_control_frame.pack(fill="x", padx=5, pady=5)
        
        ttk.Label(topview_control_frame, text="Chọn xe:").pack(side="left", padx=2)
        self.tab2_top_container = ttk.Combobox(topview_control_frame, state="readonly", width=15)
        self.tab2_top_container.pack(side="left", padx=2)
        self.tab2_top_container.bind("<<ComboboxSelected>>", self.on_tab2_top_container_change)
        
        ttk.Label(topview_control_frame, text="Chọn lớp:").pack(side="left", padx=2)
        self.tab2_top_layer = ttk.Combobox(topview_control_frame, state="readonly", width=15)
        self.tab2_top_layer.pack(side="left", padx=2)
        self.tab2_top_layer.bind("<<ComboboxSelected>>", self.on_tab2_top_layer_change)
        
        ttk.Label(topview_control_frame, text="Hiển thị:").pack(side="left", padx=2)
        self.tab2_display_mode = ttk.Combobox(topview_control_frame, state="readonly", width=15,
                                            values=["Tất cả layers", "Layer hiện tại"])
        self.tab2_display_mode.pack(side="left", padx=2)
        self.tab2_display_mode.set("Layer hiện tại")
        self.tab2_display_mode.bind("<<ComboboxSelected>>", self.on_tab2_display_mode_change)
        
        ttk.Button(topview_control_frame, text="Xuất PDF Topview", 
                  command=self.export_tab2_topview_pdf).pack(side="right", padx=5)
        
        # Tạo axes cho Topview
        self.tab2_fig_top, self.tab2_ax_top = plt.subplots(figsize=(16, 3))
        self.tab2_cv_top = FigureCanvasTkAgg(self.tab2_fig_top, master=bottom_section_frame)
        self.tab2_cv_top.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=5)
        
        # Kích hoạt zoom/pan cho các axes
        self.tab2_cv_cross.draw()
        self.tab2_cv_top.draw()
        
        # Thêm chức năng zoom/pan
        for ax in self.tab2_ax_cross:
            self.enable_zoom_pan(self.tab2_cv_cross, ax)
        self.enable_zoom_pan(self.tab2_cv_top, self.tab2_ax_top)

    def on_tab2_cross_container_change(self, event=None):
        """Xử lý khi chọn container trong phần mặt cắt Tab 2"""
        self.draw_tab2_cross_sections()

    def on_tab2_top_container_change(self, event=None):
        """Xử lý khi chọn container trong phần Topview Tab 2"""
        self.update_tab2_top_layers()
        self.draw_tab2_topview()

    def on_tab2_top_layer_change(self, event=None):
        """Xử lý khi chọn layer trong phần Topview Tab 2"""
        self.draw_tab2_topview()

    def on_tab2_display_mode_change(self, event=None):
        """Xử lý khi thay đổi chế độ hiển thị"""
        self.draw_tab2_topview()

    def update_tab2_top_layers(self):
        """Cập nhật danh sách layer cho combobox Topview"""
        if not hasattr(self, 'tab2_top_layer'):
            return
            
        container_idx = self.tab2_top_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        layers = ["Tất cả"] + [layer["name"] for layer in container["layers"]]
        
        self.tab2_top_layer['values'] = layers
        if layers:
            self.tab2_top_layer.current(0)

    def draw_tab2_cross_sections(self):
        """Vẽ 4 mặt cắt cho Tab 2"""
        if not self.result:
            return
            
        # Lấy container được chọn
        container_idx = self.tab2_cross_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()
        
        cross_positions = [2000, 5000, 8000, 11000]
        colors = ['red', 'blue', 'green', 'orange']
        
        for i, x_pos in enumerate(cross_positions):
            if i >= len(self.tab2_ax_cross):
                break
                
            ax = self.tab2_ax_cross[i]
            ax.clear()
            ax.add_patch(Rectangle((0, 0), cW, cH, fill='lightgray', edgecolor='black', alpha=0.3, linewidth=2))
            
            for layer in container["layers"]:
                for box in layer["boxes"]:
                    if box["x"] <= x_pos <= box["x"] + box["L"]:
                        y_pos = box["y"]
                        z_pos = box["z"]
                        width = box["W"]
                        height = box["H"]
                        
                        color_idx = hash(box["NoID"]) % len(colors)
                        color = colors[color_idx]
                        
                        edgecolor = 'red' if box.get("rotated", False) else 'black'
                        linewidth = 3 if box.get("rotated", False) else 1.5
                        
                        rect = Rectangle((y_pos, z_pos), width, height, 
                                       facecolor=color, edgecolor=edgecolor, 
                                       alpha=0.8, linewidth=linewidth)
                        ax.add_patch(rect)
                        
                        # Thêm visual cho item chồng
                        if box.get("stacked", False):
                            stack_level = box.get("stack_level", 1)
                            if stack_level == 2:
                                ax.add_patch(Rectangle((y_pos, z_pos), width, height, 
                                             fill=False, edgecolor='green', linewidth=3, linestyle='-'))
                            elif stack_level == 3:
                                ax.add_patch(Rectangle((y_pos, z_pos), width, height, 
                                             fill=False, edgecolor='orange', linewidth=3, linestyle='-'))
                        
                        # Thêm nhãn
                        if width * height > cW * cH * 0.001:
                            font_size = max(6, min(10, int(width * 0.02)))
                            ax.text(y_pos + width/2, z_pos + height/2, 
                                   box["NoID"], 
                                   ha='center', va='center', 
                                   fontsize=font_size, alpha=0.9, weight='bold', color='black')
            
            # Thêm nhãn Z1, Z2, Z3...
            self.add_z_labels_to_cross_section_tab2(ax, container, cW, cH)
            
            ax.set_xlim(-300, cW + 100)
            ax.set_ylim(0, cH)
            ax.set_aspect('equal')
            ax.set_title(f'Mặt cắt tại {x_pos/1000:.1f}m', fontsize=12, weight='bold')
            ax.set_xlabel('Chiều rộng container (mm)', fontsize=9)
            ax.grid(True, alpha=0.3)
        
        self.tab2_fig_cross.tight_layout(pad=3.0)
        self.tab2_cv_cross.draw()

    def add_z_labels_to_cross_section_tab2(self, ax, container, cW, cH):
        """Thêm nhãn Z1, Z2, Z3... cho mặt cắt Tab 2"""
        for layer in container["layers"]:
            z_center = layer["z"] + layer["height"] / 2
            layer_name = layer["name"].replace("Lớp ", "").replace("Z", "Z")
            
            ax.text(-200, z_center, layer_name, 
                   ha='center', va='center', 
                   fontsize=8, fontweight='bold', color='darkblue',
                   bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow", alpha=0.9, edgecolor='darkblue'))
            
            ax.axhline(y=layer["z"], color='gray', linestyle='--', alpha=0.5, linewidth=1)
            ax.axhline(y=layer["z"] + layer["height"], color='gray', linestyle='--', alpha=0.5, linewidth=1)

    def draw_tab2_topview(self):
        """Vẽ Topview cho Tab 2"""
        if not self.result:
            return
            
        # Lấy container được chọn
        container_idx = self.tab2_top_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        L = self.container_length.get()
        W = self.container_width.get()
        
        self.tab2_ax_top.clear()
        self.tab2_ax_top.add_patch(Rectangle((0, 0), L, W, fc="#F8F8FF", ec="navy", lw=3))
        
        cmap = plt.get_cmap("tab20")
        
        # Xác định layers cần hiển thị
        display_mode = self.tab2_display_mode.get()
        layer_idx = self.tab2_top_layer.current()
        
        if display_mode == "Tất cả layers" or layer_idx == 0:
            layers_to_show = container["layers"]
        else:
            if 0 < layer_idx <= len(container["layers"]):
                layers_to_show = [container["layers"][layer_idx-1]]
            else:
                layers_to_show = container["layers"]
        
        # Vẽ các boxes
        for i, layer in enumerate(layers_to_show):
            alpha = 1.0 if display_mode == "Layer hiện tại" else 0.7
            
            for box in layer["boxes"]:
                color = cmap((hash(box["NoID"]) % 20) / 20)
                
                edgecolor = 'red' if box.get("rotated", False) else 'black'
                linewidth = 3 if box.get("rotated", False) else 1.5
                
                rect = Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                               fc=color, ec=edgecolor, alpha=alpha, lw=linewidth)
                self.tab2_ax_top.add_patch(rect)
                
                # Thêm visual cho item chồng
                if box.get("stacked", False):
                    stack_level = box.get("stack_level", 1)
                    if stack_level == 2:
                        self.tab2_ax_top.add_patch(Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                                               fill=False, ec='green', lw=3, linestyle='-'))
                    elif stack_level == 3:
                        self.tab2_ax_top.add_patch(Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                                               fill=False, ec='orange', lw=3, linestyle='-'))
                    
                    if box["L"] * box["W"] > L * W * 0.005:
                        font_size = max(4, min(7, int(box["L"] * 0.015)))
                        self.tab2_ax_top.text(box["x"] + box["L"]/2, box["y"] + box["W"]/2, 
                                            f"T{stack_level}", ha='center', va='center', 
                                            fontsize=font_size, alpha=0.9, weight='bold', color='red')
                
                # Thêm nhãn
                if box["L"] * box["W"] > L * W * 0.005:
                    font_size = max(4, min(7, int(box["L"] * 0.015)))
                    text_color = 'red' if box.get("rotated", False) else 'black'
                    text_content = f"{box['NoID']}: {box['L']}x{box['W']}x{box['H']}"
                    self.tab2_ax_top.text(box["x"] + box["L"]/2, box["y"] + box["W"]/2, 
                                       text_content, ha='center', va='center', 
                                       fontsize=font_size, alpha=0.9, weight='bold', color=text_color)
        
        self.tab2_ax_top.set_xlim(-100, L + 100)
        self.tab2_ax_top.set_ylim(-100, W + 100)
        self.tab2_ax_top.set_aspect("equal")
        self.tab2_ax_top.set_xticks([])
        self.tab2_ax_top.set_yticks([])

        
        # Tiêu đề
        title = f"TOPVIEW - {container['name']}"
        if display_mode == "Layer hiện tại" and layer_idx > 0:
            title += f" - {layers_to_show[0]['name']}"
        elif display_mode == "Tất cả layers":
            title += f" - Tất cả layers"
        
        # self.tab2_ax_top.set_title(title, fontsize=14, weight='bold', pad=20)
        # self.tab2_ax_top.set_xlabel("Chiều dài container (mm)", fontsize=11)
        # self.tab2_ax_top.set_ylabel("Chiều rộng container (mm)", fontsize=11)
        self.tab2_ax_top.grid(True, alpha=0.3)
        
        # Thông tin thống kê
        total_boxes = sum(len(l["boxes"]) for l in layers_to_show)
        stacked_count = sum(1 for l in layers_to_show 
                           for b in l["boxes"] if b.get("stacked", False))
        
        info_text = f"Tổng số kiện: {total_boxes}"
        if stacked_count > 0:
            info_text += f" | Đã chồng: {stacked_count}"
        
        self.tab2_ax_top.text(0.02, 0.98, info_text, 
                             transform=self.tab2_ax_top.transAxes, fontsize=11,
                             bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.8),
                             verticalalignment='top')
        
        self.tab2_fig_top.tight_layout(pad=3.0)
        self.tab2_cv_top.draw()

    def export_tab2_topview_pdf(self):
        """Xuất PDF Topview từ Tab 2"""
        if not self.result:
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất!")
            return
            
        fp = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if fp:
            try:
                self.tab2_fig_top.savefig(fp, dpi=300, bbox_inches='tight')
                messagebox.showinfo("Thành công", f"Đã lưu Topview dưới dạng PDF!\n{fp}")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể lưu file PDF:\n{str(e)}")

    # =============================================================
    # 3D MOVEMENT FUNCTIONS - FIXED VERSION WITH ALL VIEWS LINKED
    # =============================================================
    
    def move_items_3d(self):
        import matplotlib.pyplot as plt
        plt.close("all")

        """Open window to move items in 3D with high precision (X, Y, Z) - No drag and drop"""
        if not self.result:
            messagebox.showwarning("Cảnh báo", "Chưa có kết quả tính toán! Hãy chạy tính toán xếp kiện trước.")
            return
        
        move_window = tk.Toplevel(self.root)
        move_window.title("Di chuyển Item 3D - Độ chính xác cao (X, Y, Z)")
        move_window.state("zoomed")  # Full screen
        move_window.transient(self.root)
        move_window.grab_set()
        
        # ===== MAIN CONTAINER =====
        main_container = ttk.Frame(move_window)
        main_container.pack(fill="both", expand=True, padx=10, pady=10)
        
        # ===== TOP CONTROL FRAME =====
        top_control_frame = ttk.Frame(main_container)
        top_control_frame.pack(fill="x", pady=(0, 10))
        
        # Selection controls
        selection_frame = ttk.LabelFrame(top_control_frame, text="Chọn Container và Layer")
        selection_frame.pack(side="left", fill="x", expand=True, padx=(0, 10))
        
        selection_inner = ttk.Frame(selection_frame)
        selection_inner.pack(fill="x", padx=5, pady=5)
        
        # Destination container
        ttk.Label(selection_inner, text="Container ĐÍCH:").grid(row=0, column=0, sticky="w", padx=2, pady=2)
        self.move_cb_container = ttk.Combobox(selection_inner, state="readonly", width=20)
        self.move_cb_container.grid(row=0, column=1, padx=2, pady=2)
        self.move_cb_container['values'] = [c["name"] for c in self.result]
        self.move_cb_container.current(0)
        self.move_cb_container.bind("<<ComboboxSelected>>", lambda e: self.update_move_layer_list_3d())
        
        ttk.Label(selection_inner, text="Layer ĐÍCH:").grid(row=0, column=2, sticky="w", padx=2, pady=2)
        self.move_cb_layer = ttk.Combobox(selection_inner, state="readonly", width=20)
        self.move_cb_layer.grid(row=0, column=3, padx=2, pady=2)
        self.move_cb_layer.bind("<<ComboboxSelected>>", lambda e: self.draw_move_view_3d())
        
        # Source container for transfer
        transfer_frame = ttk.LabelFrame(top_control_frame, text="Chuyển Item từ Container Khác")
        transfer_frame.pack(side="left", fill="x", expand=True)
        
        transfer_inner = ttk.Frame(transfer_frame)
        transfer_inner.pack(fill="x", padx=5, pady=5)
        
        ttk.Label(transfer_inner, text="Container NGUỒN:").grid(row=0, column=0, sticky="w", padx=2, pady=2)
        self.src_cb_container = ttk.Combobox(transfer_inner, state="readonly", width=20)
        self.src_cb_container.grid(row=0, column=1, padx=2, pady=2)
        self.src_cb_container.bind("<<ComboboxSelected>>", lambda e: self.update_src_layer_list())
        
        ttk.Label(transfer_inner, text="Layer NGUỒN:").grid(row=0, column=2, sticky="w", padx=2, pady=2)
        self.src_cb_layer = ttk.Combobox(transfer_inner, state="readonly", width=20)
        self.src_cb_layer.grid(row=0, column=3, padx=2, pady=2)
        self.src_cb_layer.bind("<<ComboboxSelected>>", lambda e: [self.update_src_item_list(), self.draw_source_views()])
        
        # ===== ACTION BUTTONS FRAME =====
        action_frame = ttk.Frame(main_container)
        action_frame.pack(fill="x", pady=(0, 10))
        
        self.save_btn = tk.Button(
            action_frame,
            text="💾 LƯU",
            command=lambda: self.save_moved_items_3d(move_window),
            bg="#4CAF50",
            fg="white",
            font=("Arial", 9, "bold"),
            padx=10,
            pady=3,
            relief="raised",
            bd=2
        )
        self.save_btn.pack(side="left", padx=2)
        
        ttk.Button(action_frame, text="🔄 XOAY 90°", command=self.rotate_selected_items_90).pack(side="left", padx=2)
        ttk.Button(action_frame, text="Chọn tất cả", command=self.select_all_items_3d).pack(side="left", padx=2)
        ttk.Button(action_frame, text="Bỏ chọn tất cả", command=self.deselect_all_items_3d).pack(side="left", padx=2)
        ttk.Button(action_frame, text="Reset vị trí", command=self.reset_move_positions_3d).pack(side="left", padx=2)
        ttk.Button(action_frame, text="Undo", command=self.undo_move_3d).pack(side="left", padx=4)
        ttk.Button(action_frame, text="Redo", command=self.redo_move_3d).pack(side="left", padx=2)
        ttk.Button(action_frame, text="Tự động sắp xếp lại", command=self.auto_rearrange_3d).pack(side="left", padx=2)
        ttk.Button(action_frame, text="📏 DIM X,Y", command=lambda: dim_module.enable_dim(self)).pack(side="left", padx=6)
        ttk.Button(action_frame, text="❌ Tắt DIM", command=lambda: dim_module.disable_dim(self)).pack(side="left", padx=2)
        ttk.Button(action_frame, text="🚫 BỎ CHỌN", command=self.clear_selected_item).pack(side="left", padx=2)
        
        # ===== MAIN DISPLAY AREA (PANED WINDOW) =====
        display_pane = ttk.PanedWindow(main_container, orient=tk.VERTICAL)
        display_pane.pack(fill="both", expand=True)
        
        # UPPER PANE: Destination container views
        upper_pane = ttk.PanedWindow(display_pane, orient=tk.HORIZONTAL)
        display_pane.add(upper_pane, weight=2)
        
        # DESTINATION CONTAINER NOTEBOOK
        dest_notebook = ttk.Notebook(upper_pane)
        upper_pane.add(dest_notebook, weight=2)
        
        # Tab 1: Top view (XY plane) - DESTINATION
        dest_top_frame = ttk.Frame(dest_notebook)
        dest_notebook.add(dest_top_frame, text="MẶT BẰNG ĐÍCH (XY)")
        self.move_fig_top, self.move_ax_top = plt.subplots(figsize=(14, 10))
        self.move_canvas_top = FigureCanvasTkAgg(self.move_fig_top, master=dest_top_frame)
        self.move_canvas_top.get_tk_widget().pack(fill="both", expand=True)
        self.enable_zoom_pan(self.move_canvas_top, self.move_ax_top)
        self.move_canvas_top.mpl_connect("button_press_event", self.on_dest_mouse_press)
        self.move_canvas_top.mpl_connect("button_release_event", self.on_dest_mouse_release)
        
        # Tab 2: Side view (XZ plane) - DESTINATION
        dest_side_frame = ttk.Frame(dest_notebook)
        dest_notebook.add(dest_side_frame, text="MẶT ĐỨNG ĐÍCH (XZ)")
        self.move_fig_side, self.move_ax_side = plt.subplots(figsize=(14, 10))
        self.move_canvas_side = FigureCanvasTkAgg(self.move_fig_side, master=dest_side_frame)
        self.move_canvas_side.get_tk_widget().pack(fill="both", expand=True)
        self.enable_zoom_pan(self.move_canvas_side, self.move_ax_side)
        
        # Tab 3: Front view (YZ plane) - DESTINATION
        dest_front_frame = ttk.Frame(dest_notebook)
        dest_notebook.add(dest_front_frame, text="MẶT CẠNH ĐÍCH (YZ)")
        self.move_fig_front, self.move_ax_front = plt.subplots(figsize=(14, 10))
        self.move_canvas_front = FigureCanvasTkAgg(self.move_fig_front, master=dest_front_frame)
        self.move_canvas_front.get_tk_widget().pack(fill="both", expand=True)
        
        # SOURCE CONTAINER NOTEBOOK
        src_notebook = ttk.Notebook(upper_pane)
        upper_pane.add(src_notebook, weight=1)
        
        # Tab 1: Top view (XY plane) - SOURCE
        src_top_frame = ttk.Frame(src_notebook)
        src_notebook.add(src_top_frame, text="MẶT BẰNG NGUỒN (XY)")
        self.src_fig_top, self.src_ax_top = plt.subplots(figsize=(14, 10))
        self.src_canvas_top = FigureCanvasTkAgg(self.src_fig_top, master=src_top_frame)
        self.src_canvas_top.get_tk_widget().pack(fill="both", expand=True)
        self.enable_zoom_pan(self.src_canvas_top, self.src_ax_top)
        self.src_canvas_top.mpl_connect('button_press_event', self.on_source_mouse_press)
        
        # Tab 2: Side view (XZ plane) - SOURCE
        src_side_frame = ttk.Frame(src_notebook)
        src_notebook.add(src_side_frame, text="MẶT ĐỨNG NGUỒN (XZ)")
        self.src_fig_side, self.src_ax_side = plt.subplots(figsize=(14, 10))
        self.src_canvas_side = FigureCanvasTkAgg(self.src_fig_side, master=src_side_frame)
        self.src_canvas_side.get_tk_widget().pack(fill="both", expand=True)
        
        # Tab 3: Front view (YZ plane) - SOURCE
        src_front_frame = ttk.Frame(src_notebook)
        src_notebook.add(src_front_frame, text="MẶT CẠNH NGUỒN (YZ)")
        self.src_fig_front, self.src_ax_front = plt.subplots(figsize=(14, 10))
        self.src_canvas_front = FigureCanvasTkAgg(self.src_fig_front, master=src_front_frame)
        self.src_canvas_front.get_tk_widget().pack(fill="both", expand=True)
        
        # LOWER PANE: Controls and item transfer
        lower_pane = ttk.PanedWindow(display_pane, orient=tk.HORIZONTAL)
        display_pane.add(lower_pane, weight=1)
        
        # LEFT: Control panel
        control_panel = ttk.LabelFrame(lower_pane, text="Điều khiển di chuyển chính xác (X, Y, Z)")
        lower_pane.add(control_panel, weight=1)
        
        # Selected items info
        info_frame = ttk.Frame(control_panel)
        info_frame.pack(fill="x", padx=5, pady=5)
        
        ttk.Label(info_frame, text="Items được chọn:").pack(side="left", padx=2)
        self.selected_item_label = ttk.Label(info_frame, text="Không có", foreground="red", font=("Arial", 10, "bold"))
        self.selected_item_label.pack(side="left", padx=2)
        
        # X controls
        x_frame = ttk.LabelFrame(control_panel, text="ĐIỀU KHIỂN TRỤC X")
        x_frame.pack(fill="x", padx=5, pady=2)
        
        x_inner = ttk.Frame(x_frame)
        x_inner.pack(fill="x", padx=5, pady=2)
        
        ttk.Label(x_inner, text="Vị trí X mới (mm):").pack(side="left", padx=2)
        self.new_x_var = tk.StringVar()
        self.new_x_entry = ttk.Entry(x_inner, textvariable=self.new_x_var, width=10, font=("Arial", 10))
        self.new_x_entry.pack(side="left", padx=2)
        self.new_x_entry.bind('<Return>', lambda e: self.move_to_exact_position_3d(axis='x'))
        
        ttk.Button(x_inner, text="Di chuyển đến X", 
                  command=lambda: self.move_to_exact_position_3d(axis='x')).pack(side="left", padx=2)
        
        ttk.Button(x_inner, text="Trái (-10)", command=lambda: self.move_selected_items_3d(-10, 0, 0)).pack(side="left", padx=2)
        ttk.Button(x_inner, text="Phải (+10)", command=lambda: self.move_selected_items_3d(10, 0, 0)).pack(side="left", padx=2)
        ttk.Button(x_inner, text="Căn trái (X=0)", command=lambda: self.move_to_exact_position_3d(x=0)).pack(side="left", padx=2)
        
        # Y controls
        y_frame = ttk.LabelFrame(control_panel, text="ĐIỀU KHIỂN TRỤC Y")
        y_frame.pack(fill="x", padx=5, pady=2)
        
        y_inner = ttk.Frame(y_frame)
        y_inner.pack(fill="x", padx=5, pady=2)
        
        ttk.Label(y_inner, text="Vị trí Y mới (mm):").pack(side="left", padx=2)
        self.new_y_var = tk.StringVar()
        self.new_y_entry = ttk.Entry(y_inner, textvariable=self.new_y_var, width=10, font=("Arial", 10))
        self.new_y_entry.pack(side="left", padx=2)
        self.new_y_entry.bind('<Return>', lambda e: self.move_to_exact_position_3d(axis='y'))
        
        ttk.Button(y_inner, text="Di chuyển đến Y", 
                  command=lambda: self.move_to_exact_position_3d(axis='y')).pack(side="left", padx=2)
        
        ttk.Button(y_inner, text="Lên (-10)", command=lambda: self.move_selected_items_3d(0, -10, 0)).pack(side="left", padx=2)
        ttk.Button(y_inner, text="Xuống (+10)", command=lambda: self.move_selected_items_3d(0, 10, 0)).pack(side="left", padx=2)
        ttk.Button(y_inner, text="Căn trên (Y=0)", command=lambda: self.move_to_exact_position_3d(y=0)).pack(side="left", padx=2)
        
        # Z controls
        z_frame = ttk.LabelFrame(control_panel, text="ĐIỀU KHIỂN TRỤC Z")
        z_frame.pack(fill="x", padx=5, pady=2)
        
        z_inner = ttk.Frame(z_frame)
        z_inner.pack(fill="x", padx=5, pady=2)
        
        ttk.Label(z_inner, text="Vị trí Z mới (mm):").pack(side="left", padx=2)
        self.new_z_var = tk.StringVar()
        self.new_z_entry = ttk.Entry(z_inner, textvariable=self.new_z_var, width=10, font=("Arial", 10))
        self.new_z_entry.pack(side="left", padx=2)
        self.new_z_entry.bind('<Return>', lambda e: self.move_to_exact_position_3d(axis='z'))
        
        ttk.Button(z_inner, text="Di chuyển đến Z", 
                  command=lambda: self.move_to_exact_position_3d(axis='z')).pack(side="left", padx=2)
        
        ttk.Button(z_inner, text="Lên cao (+10)", command=lambda: self.move_selected_items_3d(0, 0, 10)).pack(side="left", padx=2)
        ttk.Button(z_inner, text="Xuống thấp (-10)", command=lambda: self.move_selected_items_3d(0, 0, -10)).pack(side="left", padx=2)
        ttk.Button(z_inner, text="Căn đáy (Z=0)", command=lambda: self.move_to_exact_position_3d(z=0)).pack(side="left", padx=2)
        
        # ===== LAYER Z MOVEMENT CONTROLS - IMPROVED =====
        layer_frame = ttk.LabelFrame(control_panel, text="DI CHUYỂN TOÀN BỘ LAYER THEO TRỤC Z")
        layer_frame.pack(fill="x", padx=5, pady=2)
        
        # Layer info
        layer_info_frame = ttk.Frame(layer_frame)
        layer_info_frame.pack(fill="x", padx=5, pady=2)
        
        ttk.Label(layer_info_frame, text="Layer hiện tại:").pack(side="left", padx=2)
        self.current_layer_info_label = ttk.Label(layer_info_frame, text="Chưa chọn", 
                                                foreground="blue", font=("Arial", 10, "bold"))
        self.current_layer_info_label.pack(side="left", padx=2)
        
        # Layer Z position entry (with expression support)
        layer_pos_frame = ttk.Frame(layer_frame)
        layer_pos_frame.pack(fill="x", padx=5, pady=2)
        
        ttk.Label(layer_pos_frame, text="Vị trí Z mới (mm):").pack(side="left", padx=2)
        self.layer_new_z_var = tk.StringVar()
        self.layer_new_z_entry = ttk.Entry(layer_pos_frame, textvariable=self.layer_new_z_var, 
                                         width=10, font=("Arial", 10))
        self.layer_new_z_entry.pack(side="left", padx=2)
        self.layer_new_z_entry.bind('<Return>', lambda e: self.move_layer_to_exact_position())
        
        ttk.Button(layer_pos_frame, text="Áp dụng", 
                  command=self.move_layer_to_exact_position).pack(side="left", padx=2)
        
        # Layer movement buttons - STEP 1
        layer_buttons_frame1 = ttk.Frame(layer_frame)
        layer_buttons_frame1.pack(fill="x", padx=5, pady=2)
        
        ttk.Button(layer_buttons_frame1, text="Lên +10", 
                  command=lambda: self.move_current_layer_by_amount(10)).pack(side="left", padx=2)
        ttk.Button(layer_buttons_frame1, text="Xuống -10", 
                  command=lambda: self.move_current_layer_by_amount(-10)).pack(side="left", padx=2)
        ttk.Button(layer_buttons_frame1, text="Lên +100", 
                  command=lambda: self.move_current_layer_by_amount(100)).pack(side="left", padx=2)
        ttk.Button(layer_buttons_frame1, text="Xuống -100", 
                  command=lambda: self.move_current_layer_by_amount(-100)).pack(side="left", padx=2)
        
        # Layer movement buttons - STEP 2
        layer_buttons_frame2 = ttk.Frame(layer_frame)
        layer_buttons_frame2.pack(fill="x", padx=5, pady=2)
        
        ttk.Button(layer_buttons_frame2, text="Căn đáy (Z=0)", 
                  command=lambda: self.move_layer_to_exact_position(z=0)).pack(side="left", padx=2)
        ttk.Button(layer_buttons_frame2, text="Căn đỉnh", 
                  command=self.move_layer_to_top).pack(side="left", padx=2)
        ttk.Button(layer_buttons_frame2, text="Phân bố đều", 
                  command=self.distribute_layers_evenly).pack(side="left", padx=2)
        
        # RIGHT: Item transfer panel
        transfer_panel = ttk.LabelFrame(lower_pane, text="CHUYỂN ITEM TỪ CONTAINER NGUỒN")
        lower_pane.add(transfer_panel, weight=1)
        
        # Items list
        list_frame = ttk.Frame(transfer_panel)
        list_frame.pack(fill="both", expand=True, padx=5, pady=5)
        
        self.src_items_listbox = tk.Listbox(list_frame, height=6, font=("Consolas", 9), selectmode=tk.SINGLE)
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.src_items_listbox.yview)
        self.src_items_listbox.configure(yscrollcommand=scrollbar.set)
        
        self.src_items_listbox.pack(side="left", fill="both", expand=True, padx=(0, 2))
        scrollbar.pack(side="right", fill="y")
        
        # Transfer controls
        transfer_controls = ttk.Frame(transfer_panel)
        transfer_controls.pack(fill="x", padx=5, pady=5)
        
        ttk.Button(transfer_controls, text="📥 Lấy item đã chọn", 
                  command=self.transfer_selected_item).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(transfer_controls, text="📥 Lấy tất cả item trong lớp", 
                  command=self.transfer_all_layer_items).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(transfer_controls, text="🚚 Chuyển toàn bộ layer", 
                  command=self.transfer_whole_layer).pack(side="left", fill="x", expand=True, padx=2)
        
        # Position entry
        pos_frame = ttk.Frame(transfer_panel)
        pos_frame.pack(fill="x", padx=5, pady=5)
        
        ttk.Label(pos_frame, text="Xếp tại: X=").pack(side="left", padx=2)
        self.transfer_x_var = tk.StringVar(value="0")
        ttk.Entry(pos_frame, textvariable=self.transfer_x_var, width=6).pack(side="left", padx=2)
        
        ttk.Label(pos_frame, text="Y=").pack(side="left", padx=2)
        self.transfer_y_var = tk.StringVar(value="0")
        ttk.Entry(pos_frame, textvariable=self.transfer_y_var, width=6).pack(side="left", padx=2)
        
        ttk.Label(pos_frame, text="Z=").pack(side="left", padx=2)
        self.transfer_z_var = tk.StringVar()
        ttk.Entry(pos_frame, textvariable=self.transfer_z_var, width=6).pack(side="left", padx=2)
        
        # Status label
        self.transfer_status_label = ttk.Label(transfer_panel, text="Sẵn sàng chuyển item...", 
                                              foreground="blue", font=("Arial", 9, "italic"))
        self.transfer_status_label.pack(pady=2)
        
        # Connect events for source views
        self.src_cb_container.bind("<<ComboboxSelected>>", lambda e: [self.update_src_layer_list(), self.draw_source_views()])
        self.src_cb_layer.bind("<<ComboboxSelected>>", lambda e: [self.update_src_item_list(), self.draw_source_views()])
        
        # Connect events for destination views
        self.move_cb_container.bind("<<ComboboxSelected>>", lambda e: [self.update_move_layer_list_3d(), self.update_src_container_list()])
        self.move_cb_layer.bind("<<ComboboxSelected>>", lambda e: self.draw_move_view_3d())
        
        # Connect click events
        self.move_canvas_top.mpl_connect('button_press_event', self.on_move_click_3d)
        self.move_canvas_side.mpl_connect('button_press_event', self.on_move_click_3d)
        self.move_canvas_front.mpl_connect('button_press_event', self.on_move_click_3d)
        
        # Keyboard events
        self.move_canvas_top.mpl_connect('key_press_event', self.on_key_press_3d)
        self.move_canvas_top.mpl_connect('key_release_event', self.on_key_release_3d)
        
        # Initialize
        self.update_move_layer_list_3d()
        self.update_src_container_list()
        self.draw_move_view_3d()
        self.update_layer_info_3d()
        
        # Bottom close button
        bottom_frame = ttk.Frame(move_window)
        bottom_frame.pack(fill="x", padx=10, pady=10)
        
        ttk.Button(bottom_frame, text="Đóng cửa sổ", command=move_window.destroy).pack(side="right", padx=2)

    # =============================================================
    # NEW FUNCTION: TRANSFER WHOLE LAYER
    # =============================================================
    
    def transfer_whole_layer(self):
        """Chuyển toàn bộ layer từ container nguồn sang container đích"""
        # Lấy container nguồn và layer nguồn
        src_container_name = self.src_cb_container.get()
        src_layer_name = self.src_cb_layer.get()
        
        if not src_container_name or not src_layer_name:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn container nguồn và layer nguồn!")
            return
            
        # Lấy container đích
        dest_container_idx = self.move_cb_container.current()
        if dest_container_idx < 0:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn container đích!")
            return
            
        # Tìm container nguồn và container đích trong kết quả
        src_container = None
        dest_container = self.result[dest_container_idx]
        for container in self.result:
            if container["name"] == src_container_name:
                src_container = container
                break
                
        if not src_container:
            messagebox.showerror("Lỗi", "Không tìm thấy container nguồn!")
            return
            
        # Tìm layer nguồn
        src_layer = None
        for layer in src_container["layers"]:
            if layer["name"] == src_layer_name:
                src_layer = layer
                break
                
        if not src_layer:
            messagebox.showerror("Lỗi", "Không tìm thấy layer nguồn!")
            return
            
        # Kiểm tra xem container nguồn và container đích có trùng nhau không
        if src_container == dest_container:
            messagebox.showwarning("Cảnh báo", "Không thể chuyển layer trong cùng container!")
            return
            
        # Hỏi xác nhận
        if not messagebox.askyesno("Xác nhận", 
            f"Bạn có chắc muốn chuyển TOÀN BỘ layer:\n"
            f"{src_layer_name} từ {src_container_name}\n"
            f"sang container đích {dest_container['name']}?\n\n"
            f"Layer sẽ được đặt lên trên cùng với tên mới Z tiếp theo."):
            return
        
        # Lưu trạng thái để UNDO
        self.save_current_state_for_undo_3d()
        
        # Tạo tên layer mới cho container đích: Z tiếp theo
        import re
        max_z_num = 0
        for layer in dest_container["layers"]:
            match = re.match(r'Lớp Z(\d+)', layer['name'])
            if match:
                z_num = int(match.group(1))
                if z_num > max_z_num:
                    max_z_num = z_num
        
        new_layer_name = f"Lớp Z{max_z_num + 1}"
        
        # Tính vị trí Z mới cho layer: đặt trên cùng container đích
        if dest_container["layers"]:
            # Tìm layer có z lớn nhất
            max_z_layer = max(dest_container["layers"], key=lambda l: l["z"])
            new_z = max_z_layer["z"] + max_z_layer["height"]
        else:
            new_z = 0
            
        # Tạo layer mới
        new_layer = {
            "name": new_layer_name,
            "z": new_z,
            "height": src_layer["height"],
            "boxes": []
        }
        
        # Sao chép các item từ layer nguồn sang layer mới
        for box in src_layer["boxes"]:
            # Tính offset z của item so với layer nguồn
            offset_z = box["z"] - src_layer["z"]
            new_box = box.copy()
            new_box["z"] = new_z + offset_z
            new_box["uid"] = random.random()  # Tạo uid mới để tránh trùng
            new_layer["boxes"].append(new_box)
            
        # Thêm layer mới vào container đích
        dest_container["layers"].append(new_layer)
        
        # Xóa layer nguồn khỏi container nguồn
        src_container["layers"].remove(src_layer)
        
        # Cập nhật thông tin container
        self._update_container_info(src_container)
        self._update_container_info(dest_container)
        
        # Nếu container nguồn không còn layer nào, xóa container nguồn khỏi danh sách
        if not src_container["layers"]:
            self.result.remove(src_container)
            messagebox.showinfo("Thông báo", 
                f"Container {src_container_name} đã trống và đã được xóa khỏi danh sách.")
        
        # Cập nhật lại combobox container nguồn (vì có thể container đã bị xóa)
        self.update_src_container_list()
        # Cập nhật lại combobox layer nguồn
        self.update_src_layer_list()
        # Cập nhật lại combobox layer đích (vì có layer mới)
        self.update_move_layer_list_3d()
        
        # Cập nhật Tab 2 nếu đang mở
        if hasattr(self, 'tab2_cross_container'):
            self.update_tab2_controls()
        
        # Vẽ lại các view
        self.draw_source_views()
        self.draw_move_view_3d()
        
        messagebox.showinfo("Thành công", 
            f"Đã chuyển layer {src_layer_name} sang {dest_container['name']} với tên {new_layer_name}\n"
            f"Vị trí Z mới: {new_z}mm. Bạn có thể điều chỉnh Z bằng công cụ di chuyển layer.")
        
        # Cập nhật trạng thái
        self.transfer_status_label.config(
            text=f"Đã chuyển layer {src_layer_name} sang {dest_container['name']}",
            foreground="green"
        )

    def _update_container_info(self, container):
        """Cập nhật thông tin container (packed_count, packed_vol)"""
        all_boxes = []
        for layer in container["layers"]:
            all_boxes.extend(layer["boxes"])
        container["packed_count"] = len(all_boxes)
        container["packed_vol"] = sum(box["L"] * box["W"] * box["H"] for box in all_boxes)

    # =============================================================
    # VIEW DRAWING FUNCTIONS - FIXED AND LINKED
    # =============================================================
    
    def draw_move_view_3d(self):
        """Draw 3 views for destination container"""
        # Clear all axes
        self.move_ax_top.clear()
        self.move_ax_side.clear()
        self.move_ax_front.clear()
        
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        
        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()
        
        cmap = plt.get_cmap("tab20")
        
        # 1. Top View (XY plane)
        self.move_ax_top.add_patch(Rectangle((0, 0), cL, cW, fc="#F8F8FF", ec="navy", lw=3))
        
        for i, box in enumerate(layer["boxes"]):
            color = cmap((hash(box["NoID"]) % 20) / 20)
            
            if i in self.selected_item_indices:
                edgecolor = 'red'
                linewidth = 4
            elif box.get("rotated", False):
                edgecolor = 'red'
                linewidth = 2
            else:
                edgecolor = 'black'
                linewidth=2.2
            
            rect = Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                           fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
            self.move_ax_top.add_patch(rect)
            
            # Stacking visualization
            if box.get("stacked", False):
                stack_level = box.get("stack_level", 1)
                if stack_level == 2:
                    self.move_ax_top.add_patch(Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                                           fill=False, ec='green', lw=3, linestyle='-'))
                elif stack_level == 3:
                    self.move_ax_top.add_patch(Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                                           fill=False, ec='orange', lw=3, linestyle='-'))
            
            # Text label
            if box["L"] * box["W"] > cL * cW * 0.01:
                font_size = max(4, min(7, int(box["L"] * 0.02)))
                text_color = 'red' if i in self.selected_item_indices else ('red' if box.get("rotated", False) else 'black')
                text_content = f"{box['NoID']}: {box['L']}x{box['W']}x{box['H']}"
                self.move_ax_top.text(box["x"] + box["L"]/2, box["y"] + box["W"]/2, 
                               text_content, ha='center', va='center', 
                               fontsize=font_size, alpha=0.9, weight='bold', color=text_color)
        
        self.move_ax_top.set_xlim(-50, cL + 50)
        self.move_ax_top.set_ylim(-50, cW + 50)
        self.move_ax_top.set_aspect("equal")
        self.move_ax_top.set_title(f"TOP VIEW ĐÍCH - {container['name']} - {layer['name']}", 
                         fontsize=14, weight='bold', pad=20)
        self.move_ax_top.set_xlabel("Chiều dài container (mm) - TRỤC X", fontsize=6.25)
        self.move_ax_top.grid(True, alpha=0.3)
        
        # 2. Side View (XZ plane)
        self.move_ax_side.add_patch(Rectangle((0, 0), cL, cH, fc="#FFFAF0", ec="brown", lw=3))
        
        for i, box in enumerate(layer["boxes"]):
            color = cmap((hash(box["NoID"]) % 20) / 20)
            
            if i in self.selected_item_indices:
                edgecolor = 'red'
                linewidth = 4
            elif box.get("rotated", False):
                edgecolor = 'red'
                linewidth = 2
            else:
                edgecolor = 'black'
                linewidth=2.2
            
            rect = Rectangle((box["x"], box["z"]), box["L"], box["H"], 
                           fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
            self.move_ax_side.add_patch(rect)
            
            if box.get("stacked", False):
                stack_level = box.get("stack_level", 1)
                if stack_level == 2:
                    self.move_ax_side.add_patch(Rectangle((box["x"], box["z"]), box["L"], box["H"], 
                                           fill=False, ec='green', lw=3, linestyle='-'))
                elif stack_level == 3:
                    self.move_ax_side.add_patch(Rectangle((box["x"], box["z"]), box["L"], box["H"], 
                                           fill=False, ec='orange', lw=3, linestyle='-'))
        
        self.move_ax_side.set_xlim(-50, cL + 50)
        self.move_ax_side.set_ylim(-50, cH + 50)
        self.move_ax_side.set_aspect("equal")
        self.move_ax_side.set_title(f"SIDE VIEW ĐÍCH (XZ) - {container['name']} - {layer['name']}", 
                         fontsize=14, weight='bold', pad=20)
        self.move_ax_side.set_xlabel("Chiều dài container (mm) - TRỤC X", fontsize=6.25)
        self.move_ax_side.grid(True, alpha=0.3)
        
        # 3. Front View (YZ plane)
        self.move_ax_front.add_patch(Rectangle((0, 0), cW, cH, fc="#F0FFF0", ec="darkgreen", lw=3))
        
        for i, box in enumerate(layer["boxes"]):
            color = cmap((hash(box["NoID"]) % 20) / 20)
            
            if i in self.selected_item_indices:
                edgecolor = 'red'
                linewidth = 4
            elif box.get("rotated", False):
                edgecolor = 'red'
                linewidth = 2
            else:
                edgecolor = 'black'
                linewidth=2.2
            
            rect = Rectangle((box["y"], box["z"]), box["W"], box["H"], 
                           fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
            self.move_ax_front.add_patch(rect)
        
        self.move_ax_front.set_xlim(-50, cW + 50)
        self.move_ax_front.set_ylim(-50, cH + 50)
        self.move_ax_front.set_aspect("equal")
        self.move_ax_front.set_title(f"FRONT VIEW ĐÍCH (YZ) - {container['name']} - {layer['name']}", 
                         fontsize=14, weight='bold', pad=20)
        self.move_ax_front.set_xlabel("Chiều rộng container (mm) - TRỤC Y", fontsize=6.25)
        self.move_ax_front.grid(True, alpha=0.3)
        
        # Draw all canvases
        self.move_canvas_top.draw()
        self.move_canvas_side.draw()
        self.move_canvas_front.draw()
        
        self.update_selection_info_3d()
        self.update_layer_info_3d()

    def draw_source_views(self):
        """Draw 3 views for source container"""
        # Clear all axes
        self.src_ax_top.clear()
        self.src_ax_side.clear()
        self.src_ax_front.clear()
        
        src_container_name = self.src_cb_container.get()
        src_layer_name = self.src_cb_layer.get()
        
        if not src_container_name or not src_layer_name:
            return
            
        # Find source container
        src_container = None
        for container in self.result:
            if container["name"] == src_container_name:
                src_container = container
                break
                
        if not src_container:
            return
            
        # Find source layer
        src_layer = None
        for layer in src_container["layers"]:
            if layer["name"] == src_layer_name:
                src_layer = layer
                break
                
        if not src_layer:
            return
            
        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()
        
        cmap = plt.get_cmap("tab20")
        
        # 1. Top View (XY plane) - SOURCE
        self.src_ax_top.add_patch(Rectangle((0, 0), cL, cW, fc="#F8F8FF", ec="navy", lw=3))
        
        for j, box in enumerate(src_layer["boxes"]):
            color = cmap((hash(box["NoID"]) % 20) / 20)
            
            edgecolor = 'red' if (j == getattr(self,'selected_source_index',None) or box.get("rotated", False)) else 'black'
            linewidth = 2 if box.get("rotated", False) else 1.2
            
            rect = Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                           fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
            self.src_ax_top.add_patch(rect)
            
            if box.get("stacked", False):
                stack_level = box.get("stack_level", 1)
                if stack_level == 2:
                    self.src_ax_top.add_patch(Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                                           fill=False, ec='green', lw=3, linestyle='-'))
                elif stack_level == 3:
                    self.src_ax_top.add_patch(Rectangle((box["x"], box["y"]), box["L"], box["W"], 
                                           fill=False, ec='orange', lw=3, linestyle='-'))
            
            if box["L"] * box["W"] > cL * cW * 0.01:
                font_size = max(4, min(7, int(box["L"] * 0.02)))
                text_content = f"{box['NoID']}: {box['L']}x{box['W']}x{box['H']}"
                self.src_ax_top.text(box["x"] + box["L"]/2, box["y"] + box["W"]/2, 
                               text_content, ha='center', va='center', 
                               fontsize=font_size, alpha=0.9, weight='bold', color='black')
        
        self.src_ax_top.set_xlim(-50, cL + 50)
        self.src_ax_top.set_ylim(-50, cW + 50)
        self.src_ax_top.set_aspect("equal")
        self.src_ax_top.set_title(f"TOP VIEW NGUỒN - {src_container_name} - {src_layer_name}", 
                         fontsize=14, weight='bold', pad=20)
        self.src_ax_top.set_xlabel("Chiều dài container (mm) - TRỤC X", fontsize=6.25)
        self.src_ax_top.grid(True, alpha=0.3)
        
        # 2. Side View (XZ plane) - SOURCE
        self.src_ax_side.add_patch(Rectangle((0, 0), cL, cH, fc="#FFFAF0", ec="brown", lw=3))
        
        for j, box in enumerate(src_layer["boxes"]):
            color = cmap((hash(box["NoID"]) % 20) / 20)
            
            edgecolor = 'red' if (j == self.selected_source_index or box.get("rotated", False)) else 'black'
            linewidth = 2 if box.get("rotated", False) else 1.2
            
            rect = Rectangle((box["x"], box["z"]), box["L"], box["H"], 
                           fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
            self.src_ax_side.add_patch(rect)
            
            if box.get("stacked", False):
                stack_level = box.get("stack_level", 1)
                if stack_level == 2:
                    self.src_ax_side.add_patch(Rectangle((box["x"], box["z"]), box["L"], box["H"], 
                                           fill=False, ec='green', lw=3, linestyle='-'))
                elif stack_level == 3:
                    self.src_ax_side.add_patch(Rectangle((box["x"], box["z"]), box["L"], box["H"], 
                                           fill=False, ec='orange', lw=3, linestyle='-'))
        
        self.src_ax_side.set_xlim(-50, cL + 50)
        self.src_ax_side.set_ylim(-50, cH + 50)
        self.src_ax_side.set_aspect("equal")
        self.src_ax_side.set_title(f"SIDE VIEW NGUỒN (XZ) - {src_container_name} - {src_layer_name}", 
                         fontsize=14, weight='bold', pad=20)
        self.src_ax_side.set_xlabel("Chiều dài container (mm) - TRỤC X", fontsize=6.25)
        self.src_ax_side.grid(True, alpha=0.3)
        
        # 3. Front View (YZ plane) - SOURCE
        self.src_ax_front.add_patch(Rectangle((0, 0), cW, cH, fc="#F0FFF0", ec="darkgreen", lw=3))
        
        for box in src_layer["boxes"]:
            color = cmap((hash(box["NoID"]) % 20) / 20)
            
            edgecolor = 'red' if box.get("rotated", False) else 'black'
            linewidth = 2 if box.get("rotated", False) else 1.2
            
            rect = Rectangle((box["y"], box["z"]), box["W"], box["H"], 
                           fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
            self.src_ax_front.add_patch(rect)
        
        self.src_ax_front.set_xlim(-50, cW + 50)
        self.src_ax_front.set_ylim(-50, cH + 50)
        self.src_ax_front.set_aspect("equal")
        self.src_ax_front.set_title(f"FRONT VIEW NGUỒN (YZ) - {src_container_name} - {src_layer_name}", 
                         fontsize=14, weight='bold', pad=20)
        self.src_ax_front.set_xlabel("Chiều rộng container (mm) - TRỤC Y", fontsize=6.25)
        self.src_ax_front.grid(True, alpha=0.3)
        
        # Draw all canvases
        self.src_canvas_top.draw()
        self.src_canvas_side.draw()
        self.src_canvas_front.draw()

    # =============================================================
    # TRANSFER ITEMS BETWEEN CONTAINERS FUNCTIONS
    # =============================================================
    
    def update_src_container_list(self):
        """Update source container list excluding current container"""
        if not hasattr(self, 'src_cb_container'):
            return
            
        current_container_idx = self.move_cb_container.current()
        if current_container_idx < 0:
            return
            
        current_container_name = self.result[current_container_idx]["name"]
        
        # Get all containers
        src_containers = [container["name"] for container in self.result]
        self.src_cb_container['values'] = src_containers
        if src_containers:
            self.src_cb_container.current(0)
            self.update_src_layer_list()
            self.draw_source_views()
    
    def update_src_layer_list(self):
        """Update source layer list based on selected source container"""
        if not hasattr(self, 'src_cb_container') or not hasattr(self, 'src_cb_layer'):
            return
            
        src_container_name = self.src_cb_container.get()
        if not src_container_name:
            return
            
        # Find source container
        src_container = None
        for container in self.result:
            if container["name"] == src_container_name:
                src_container = container
                break
                
        if not src_container:
            return
            
        # Update layer list
        layers = [layer["name"] for layer in src_container["layers"]]
        self.src_cb_layer['values'] = layers
        if layers:
            self.src_cb_layer.current(0)
            self.update_src_item_list()
            self.draw_source_views()
    
    def update_src_item_list(self):
        """Update item list in source layer"""
        if not hasattr(self, 'src_items_listbox'):
            return
            
        # Clear listbox
        self.src_items_listbox.delete(0, tk.END)
        
        # Get source container and layer
        src_container_name = self.src_cb_container.get()
        src_layer_name = self.src_cb_layer.get()
        
        if not src_container_name or not src_layer_name:
            return
            
        # Find source container and layer
        src_container = None
        for container in self.result:
            if container["name"] == src_container_name:
                src_container = container
                break
                
        if not src_container:
            return
            
        src_layer = None
        for layer in src_container["layers"]:
            if layer["name"] == src_layer_name:
                src_layer = layer
                break
                
        if not src_layer:
            return
            
        # Populate listbox with items
        for i, box in enumerate(src_layer["boxes"]):
            item_text = f"{box['NoID']}: {box['L']}x{box['W']}x{box['H']} - Pos: ({box['x']},{box['y']},{box['z']})"
            if box.get("rotated", False):
                item_text += " [R]"
            if box.get("stacked", False):
                item_text += f" [T{box.get('stack_level', 1)}]"
            self.src_items_listbox.insert(tk.END, item_text)
            
        # Update transfer Z position to match current layer Z
        dest_container_idx = self.move_cb_container.current()
        dest_layer_idx = self.move_cb_layer.current()
        
        if dest_container_idx >= 0 and dest_layer_idx >= 0:
            dest_container = self.result[dest_container_idx]
            dest_layer = dest_container["layers"][dest_layer_idx]
            self.transfer_z_var.set(str(dest_layer["z"]))
            
        self.transfer_status_label.config(
            text=f"Đã tìm thấy {len(src_layer['boxes'])} items trong {src_layer_name}",
            foreground="green"
        )

    def transfer_selected_item(self):
        """Transfer selected item from source to destination container/layer"""
        # Get selected item from listbox
        selected_indices = self.src_items_listbox.curselection()
        if not selected_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn item cần chuyển từ danh sách!")
            return
            
        selected_idx = selected_indices[0]
        
        # Get source container and layer
        src_container_name = self.src_cb_container.get()
        src_layer_name = self.src_cb_layer.get()
        
        if not src_container_name or not src_layer_name:
            return
            
        # Find source container and layer
        src_container = None
        src_container_idx = -1
        for idx, container in enumerate(self.result):
            if container["name"] == src_container_name:
                src_container = container
                src_container_idx = idx
                break
                
        if not src_container:
            return
            
        src_layer = None
        src_layer_idx = -1
        for idx, layer in enumerate(src_container["layers"]):
            if layer["name"] == src_layer_name:
                src_layer = layer
                src_layer_idx = idx
                break
                
        if not src_layer:
            return
            
        # Get destination container and layer
        dest_container_idx = self.move_cb_container.current()
        dest_layer_idx = self.move_cb_layer.current()
        
        if dest_container_idx < 0 or dest_layer_idx < 0:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn container và lớp đích trước!")
            return
            
        dest_container = self.result[dest_container_idx]
        dest_layer = dest_container["layers"][dest_layer_idx]
        
        # Check if source and destination are the same
        if src_container_idx == dest_container_idx and src_layer_idx == dest_layer_idx:
            messagebox.showwarning("Cảnh báo", "Không thể chuyển item trong cùng lớp!")
            return
            
        # Get the selected box
        if selected_idx >= len(src_layer["boxes"]):
            return
            
        src_box = src_layer["boxes"][selected_idx]
        
        # Get transfer position
        try:
            transfer_x = int(self.transfer_x_var.get())
            transfer_y = int(self.transfer_y_var.get())
            transfer_z = int(self.transfer_z_var.get())
        except ValueError:
            messagebox.showerror("Lỗi", "Vui lòng nhập tọa độ hợp lệ (số nguyên)!")
            return
            
        # Check if position is within container bounds
        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()
        
        if (transfer_x < 0 or transfer_x + src_box["L"] > cL or
            transfer_y < 0 or transfer_y + src_box["W"] > cW or
            transfer_z < 0 or transfer_z + src_box["H"] > cH):
            if not messagebox.askyesno("Cảnh báo", 
                f"Item có thể nằm ngoài container!\n"
                f"Container: {cL}x{cW}x{cH}mm\n"
                f"Item: {src_box['L']}x{src_box['W']}x{src_box['H']}mm\n"
                f"Vị trí: ({transfer_x},{transfer_y},{transfer_z})\n\n"
                f"Tiếp tục?"):
                return
        
        # Save state for undo
        self.save_current_state_for_undo_3d()
        
        # Create a copy of the box with new UID and position
        new_box = src_box.copy()
        new_box["uid"] = random.random()  # New unique ID
        new_box["x"] = transfer_x
        new_box["y"] = transfer_y
        new_box["z"] = transfer_z
        
        # Add to destination layer
        dest_layer["boxes"].append(new_box)
        
        # Remove from source layer
        src_layer["boxes"].pop(selected_idx)
        
        # Update displays
        self.update_src_item_list()
        self.draw_source_views()
        self.draw_move_view_3d()
        
        # Select the new item
        self.selected_item_indices = [len(dest_layer["boxes"]) - 1]
        self.update_selection_info_3d()
        
        self.transfer_status_label.config(
            text=f"Đã chuyển {src_box['NoID']} sang {dest_layer['name']}",
            foreground="green"
        )
        
        messagebox.showinfo("Thành công", f"Đã chuyển item {src_box['NoID']} thành công!")

    def transfer_all_layer_items(self):
        """Transfer all items from source layer to destination layer"""
        # Get source container and layer
        src_container_name = self.src_cb_container.get()
        src_layer_name = self.src_cb_layer.get()
        
        if not src_container_name or not src_layer_name:
            return
            
        # Find source container and layer
        src_container = None
        src_container_idx = -1
        for idx, container in enumerate(self.result):
            if container["name"] == src_container_name:
                src_container = container
                src_container_idx = idx
                break
                
        if not src_container:
            return
            
        src_layer = None
        src_layer_idx = -1
        for idx, layer in enumerate(src_container["layers"]):
            if layer["name"] == src_layer_name:
                src_layer = layer
                src_layer_idx = idx
                break
                
        if not src_layer or not src_layer["boxes"]:
            messagebox.showwarning("Cảnh báo", "Lớp nguồn không có item nào!")
            return
            
        # Get destination container and layer
        dest_container_idx = self.move_cb_container.current()
        dest_layer_idx = self.move_cb_layer.current()
        
        if dest_container_idx < 0 or dest_layer_idx < 0:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn container và lớp đích trước!")
            return
            
        dest_container = self.result[dest_container_idx]
        dest_layer = dest_container["layers"][dest_layer_idx]
        
        # Check if source and destination are the same
        if src_container_idx == dest_container_idx and src_layer_idx == dest_layer_idx:
            messagebox.showwarning("Cảnh báo", "Không thể chuyển item trong cùng lớp!")
            return
            
        # Get transfer position
        try:
            transfer_x = int(self.transfer_x_var.get())
            transfer_y = int(self.transfer_y_var.get())
            transfer_z = int(self.transfer_z_var.get())
        except ValueError:
            messagebox.showerror("Lỗi", "Vui lòng nhập tọa độ hợp lệ (số nguyên)!")
            return
            
        # Ask for confirmation
        if not messagebox.askyesno("Xác nhận", 
            f"Bạn có chắc muốn chuyển TẤT CẢ {len(src_layer['boxes'])} items từ:\n"
            f"{src_container_name}/{src_layer_name}\n"
            f"sang:\n"
            f"{dest_container['name']}/{dest_layer['name']}?\n\n"
            f"Vị trí bắt đầu: ({transfer_x},{transfer_y},{transfer_z})"):
            return
        
        # Save state for undo
        self.save_current_state_for_undo_3d()
        
        transferred_count = 0
        current_x = transfer_x
        current_y = transfer_y
        
        # Transfer each item
        for src_box in src_layer["boxes"][:]:  # Use copy for iteration
            # Create a copy with new UID
            new_box = src_box.copy()
            new_box["uid"] = random.random()
            new_box["x"] = current_x
            new_box["y"] = current_y
            new_box["z"] = transfer_z
            
            # Check if position is valid
            cL = self.container_length.get()
            cW = self.container_width.get()
            
            if current_x + new_box["L"] > cL:
                # Move to next row
                current_x = transfer_x
                current_y += new_box["W"]
                
                if current_y + new_box["W"] > cW:
                    # No more space
                    messagebox.showwarning("Cảnh báo", 
                        f"Chỉ chuyển được {transferred_count} items, không đủ không gian!")
                    break
                
                new_box["x"] = current_x
                new_box["y"] = current_y
            
            # Add to destination
            dest_layer["boxes"].append(new_box)
            current_x += new_box["L"]
            transferred_count += 1
        
        # Remove all transferred items from source
        src_layer["boxes"] = []
        
        # Update displays
        self.update_src_item_list()
        self.draw_source_views()
        self.draw_move_view_3d()
        
        messagebox.showinfo("Thành công", 
            f"Đã chuyển {transferred_count} items từ {src_layer_name} "
            f"sang {dest_layer['name']}")
        
        self.transfer_status_label.config(
            text=f"Đã chuyển {transferred_count} items sang {dest_layer['name']}",
            foreground="green"
        )

    # =============================================================
    # LAYER Z-AXIS MOVEMENT FUNCTIONS - IMPROVED
    # =============================================================
    
    def update_layer_info_3d(self):
        """Update layer information display"""
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx >= 0 and layer_idx >= 0:
            container = self.result[container_idx]
            layer = container["layers"][layer_idx]
            
            stacked_count = sum(1 for box in layer["boxes"] if box.get("stacked", False))
            
            layer_info = f"{layer['name']} - Z={layer['z']}mm - Cao: {layer['height']}mm - {len(layer['boxes'])} kiện"
            if stacked_count > 0:
                layer_info += f" ({stacked_count} chồng)"
            
            self.current_layer_info_label.config(text=layer_info)
            
            # Update layer Z entry with current Z position
            self.layer_new_z_var.set(str(layer["z"]))
    
    def move_layer_to_exact_position(self, z=None):
        """Move current layer to exact Z position (supports math expressions)"""
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        if z is None:
            # Get Z from entry field (supports math expressions)
            try:
                z = self._eval_math_expr(self.layer_new_z_var.get())
            except Exception:
                messagebox.showerror("Lỗi", "Biểu thức không hợp lệ!\nVí dụ: 523+27, 1000-250, (200+40)*2")
                return
        
        # Save state for undo
        self.save_current_state_for_undo_3d()
        
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cH = self.container_height.get()
        
        # Calculate delta Z
        delta_z = z - layer["z"]
        
        if delta_z == 0:
            return
            
        # Check if movement is within container bounds
        new_layer_z = layer["z"] + delta_z
        
        # Check all boxes in layer for boundaries
        for box in layer["boxes"]:
            new_z = box["z"] + delta_z
            if new_z < 0 or new_z + box["H"] > cH:
                messagebox.showerror("Lỗi", 
                    f"Không thể di chuyển layer vượt quá giới hạn container!\n"
                    f"Item {box['NoID']} sẽ ở Z={new_z}mm (giới hạn: 0-{cH-box['H']}mm)")
                return
        
        # Also check for collisions with other layers
        if not self.check_layer_collision(container, layer_idx, delta_z):
            if not messagebox.askyesno("Cảnh báo", 
                "Di chuyển layer có thể gây chồng chéo với layer khác.\nTiếp tục?"):
                return
        
        # Move all boxes in layer
        for box in layer["boxes"]:
            box["z"] += delta_z
        
        # Update layer Z position
        layer["z"] = new_layer_z
        
        # Update display
        self.draw_move_view_3d()
        self.update_layer_info_3d()
        
        messagebox.showinfo("Thành công", f"Đã di chuyển {layer['name']} đến Z={layer['z']}mm")
    
    def move_current_layer_by_amount(self, delta_z):
        """Move current layer by specified amount (positive = up, negative = down)"""
        if delta_z == 0:
            return
            
        # Save state for undo
        self.save_current_state_for_undo_3d()
        
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cH = self.container_height.get()
        
        # Check if movement is within container bounds
        new_layer_z = layer["z"] + delta_z
        
        # Check all boxes in layer for boundaries
        for box in layer["boxes"]:
            new_z = box["z"] + delta_z
            if new_z < 0 or new_z + box["H"] > cH:
                messagebox.showerror("Lỗi", 
                    f"Không thể di chuyển layer vượt quá giới hạn container!\n"
                    f"Item {box['NoID']} sẽ ở Z={new_z}mm (giới hạn: 0-{cH-box['H']}mm)")
                return
        
        # Also check for collisions with other layers
        if not self.check_layer_collision(container, layer_idx, delta_z):
            if not messagebox.askyesno("Cảnh báo", 
                "Di chuyển layer có thể gây chồng chéo với layer khác.\nTiếp tục?"):
                return
        
        # Move all boxes in layer
        for box in layer["boxes"]:
            box["z"] += delta_z
        
        # Update layer Z position
        layer["z"] = new_layer_z
        
        # Update display
        self.draw_move_view_3d()
        self.update_layer_info_3d()
        
        messagebox.showinfo("Thành công", f"Đã di chuyển {layer['name']} {delta_z:+d}mm")
    
    def move_layer_to_top(self):
        """Move current layer to top of container"""
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cH = self.container_height.get()
        
        # Calculate top position
        top_z = cH - layer["height"]
        
        if top_z < 0:
            top_z = 0
            
        # Move layer to top
        self.move_layer_to_exact_position(z=top_z)

    def check_layer_collision(self, container, layer_idx, delta_z):
        """Check if moving layer will collide with other layers"""
        current_layer = container["layers"][layer_idx]
        new_layer_z = current_layer["z"] + delta_z
        new_layer_top = new_layer_z + current_layer["height"]
        
        for i, other_layer in enumerate(container["layers"]):
            if i == layer_idx:
                continue
                
            other_layer_top = other_layer["z"] + other_layer["height"]
            other_layer_bottom = other_layer["z"]
            
            # Check for overlap
            if (new_layer_z < other_layer_top and new_layer_top > other_layer_bottom):
                return False
        
        return True

    def distribute_layers_evenly(self):
        """Distribute all layers evenly in container height"""
        container_idx = self.move_cb_container.current()
        if container_idx < 0:
            return
            
        # Save state for undo
        self.save_current_state_for_undo_3d()
        
        container = self.result[container_idx]
        cH = self.container_height.get()
        
        # Calculate total height of all layers
        total_layers_height = sum(layer["height"] for layer in container["layers"])
        
        if total_layers_height > cH:
            messagebox.showerror("Lỗi", 
                f"Tổng chiều cao các layer ({total_layers_height}mm) vượt quá chiều cao container ({cH}mm)!")
            return
        
        # Calculate available space and gap
        available_space = cH - total_layers_height
        gap_count = len(container["layers"]) - 1
        gap_between = available_space / (gap_count + 1) if gap_count > 0 else available_space / 2
        
        # Distribute layers evenly from bottom
        current_z = gap_between
        for layer in container["layers"]:
            # Calculate delta Z for this layer
            delta_z = current_z - layer["z"]
            
            # Move all boxes in layer
            for box in layer["boxes"]:
                box["z"] += delta_z
            
            # Update layer Z position
            layer["z"] = current_z
            
            # Move to next position
            current_z += layer["height"] + gap_between
        
        # Update display
        self.draw_move_view_3d()
        self.update_layer_info_3d()
        
        messagebox.showinfo("Thành công", "Đã dàn đều các layer trong container!")

    # ===== Drag & Drop handlers between Source/Dest Top Views =====
    def on_source_mouse_press(self, event):
        """Mouse press on TOP VIEW NGUỒN - chọn item để kéo"""
        if not event.inaxes:
            return

        container_name = self.src_cb_container.get()
        layer_name = self.src_cb_layer.get()
        if not container_name or not layer_name:
            return

        # Tìm container và layer nguồn
        src_container = None
        for c in self.result:
            if c["name"] == container_name:
                src_container = c
                break
        if not src_container:
            return

        src_layer = None
        for l in src_container["layers"]:
            if l["name"] == layer_name:
                src_layer = l
                break
        if not src_layer:
            return

        if event.xdata is None or event.ydata is None:
            return

        # Xác định box được click
        for i, box in enumerate(src_layer["boxes"]):
            if (box["x"] <= event.xdata <= box["x"] + box["L"] and
                box["y"] <= event.ydata <= box["y"] + box["W"]):
                self.dragged_item = i
                self.drag_source = "source"
                self.selected_source_index = i
                self.draw_source_views()
                return
                self.selected_source_index = i
                self.draw_source_views()

    def on_dest_mouse_press(self, event):
        """Hiện tại chưa dùng – để dành nếu muốn kéo trong đích"""
        return

    def on_dest_mouse_release(self, event):
        self.save_current_state_for_undo_3d()
        """Thả chuột trên TOP VIEW ĐÍCH để thả item kéo từ nguồn sang"""
        if not event.inaxes:
            return
        if self.dragged_item is None or self.drag_source != "source":
            return

        # Lấy thông tin layer nguồn
        src_container_name = self.src_cb_container.get()
        src_layer_name = self.src_cb_layer.get()
        if not src_container_name or not src_layer_name:
            return

        src_container = None
        for c in self.result:
            if c["name"] == src_container_name:
                src_container = c
                break
        if not src_container:
            return

        src_layer = None
        for l in src_container["layers"]:
            if l["name"] == src_layer_name:
                src_layer = l
                break
        if not src_layer:
            return

        if self.dragged_item < 0 or self.dragged_item >= len(src_layer["boxes"]):
            self.dragged_item = None
            self.drag_source = None
            return

        dragged_box = src_layer["boxes"][self.dragged_item]

        # Lấy layer đích hiện tại
        dest_container_idx = self.move_cb_container.current()
        dest_layer_idx = self.move_cb_layer.current()
        if dest_container_idx < 0 or dest_layer_idx < 0:
            self.dragged_item = None
            self.drag_source = None
            return

        dest_container = self.result[dest_container_idx]
        dest_layer = dest_container["layers"][dest_layer_idx]

        if event.xdata is None or event.ydata is None:
            self.dragged_item = None
            self.drag_source = None
            return

        # Tạo box mới với vị trí X,Y theo điểm thả, Z theo layer đích
        new_box = dragged_box.copy()
        new_box["uid"] = random.random()
        new_box["x"] = int(event.xdata)
        new_box["y"] = int(event.ydata)
        new_box["z"] = dest_layer["z"]

        dest_layer["boxes"].append(new_box)
        src_layer["boxes"].pop(self.dragged_item)

        # Reset trạng thái kéo thả
        self.dragged_item = None
        self.drag_source = None

        # Cập nhật màn hình
        self.draw_source_views()
        self.draw_move_view_3d()
        self.update_selection_info_3d()

    # =============================================================
    # 3D MOVEMENT CORE FUNCTIONS
    # =============================================================
    
    def on_key_press_3d(self, event):
        """Handle key press event for 3D movement"""
        if event.key == 'control':
            self.ctrl_pressed = True

    def on_key_release_3d(self, event):
        """Handle key release event for 3D movement"""
        if event.key == 'control':
            self.ctrl_pressed = False

    def on_move_click_3d(self, event):
        """Handle mouse click for selecting items in 3D"""
        # Nếu đang ở chế độ DIM thì bỏ qua chọn item
        # để tránh vẽ lại hình và làm mất zoom khi DIM TOPVIEW ĐÍCH
        if getattr(self, "dim_mode", False):
            return

        if event.inaxes not in [self.move_ax_top, self.move_ax_side, self.move_ax_front]:
            return

        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()

        if container_idx < 0 or layer_idx < 0:
            return

        container = self.result[container_idx]
        layer = container["layers"][layer_idx]

        clicked_item_idx = None
        current_ax = event.inaxes

        if current_ax == self.move_ax_top:
            # Top view: check XY coordinates
            for i, box in enumerate(layer["boxes"]):
                if (box["x"] <= event.xdata <= box["x"] + box["L"]
                        and box["y"] <= event.ydata <= box["y"] + box["W"]):
                    clicked_item_idx = i
                    break
        elif current_ax == self.move_ax_side:
            # Side view: check XZ coordinates
            for i, box in enumerate(layer["boxes"]):
                if (box["x"] <= event.xdata <= box["x"] + box["L"]
                        and box["z"] <= event.ydata <= box["z"] + box["H"]):
                    clicked_item_idx = i
                    break
        elif current_ax == self.move_ax_front:
            # Front view: check YZ coordinates
            for i, box in enumerate(layer["boxes"]):
                if (box["y"] <= event.xdata <= box["y"] + box["W"]
                        and box["z"] <= event.ydata <= box["z"] + box["H"]):
                    clicked_item_idx = i
                    break

        if clicked_item_idx is not None:
            if self.ctrl_pressed:
                if clicked_item_idx in self.selected_item_indices:
                    self.selected_item_indices.remove(clicked_item_idx)
                else:
                    self.selected_item_indices.append(clicked_item_idx)
            else:
                if clicked_item_idx not in self.selected_item_indices:
                    self.selected_item_indices = [clicked_item_idx]
        else:
            if not self.ctrl_pressed:
                self.selected_item_indices = []

        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def update_move_layer_list_3d(self):
        """Update layer list in 3D move window"""
        if not hasattr(self, 'move_cb_layer'):
            return
            
        container_idx = self.move_cb_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        layers = [l["name"] for l in container["layers"]]
        
        self.move_cb_layer['values'] = layers
        if layers:
            self.move_cb_layer.current(0)
            self.draw_move_view_3d()
            self.update_layer_info_3d()

    def update_selection_info_3d(self):
        """Update information about selected items in 3D"""
        if not self.selected_item_indices:
            self.selected_item_label.config(text="Không có")
            self.new_x_var.set("")
            self.new_y_var.set("")
            self.new_z_var.set("")
            return
            
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        
        if len(self.selected_item_indices) == 1:
            box = layer["boxes"][self.selected_item_indices[0]]
            self.selected_item_label.config(
                text=f"{box['NoID']}: {box['L']}x{box['W']}x{box['H']}mm - X={box['x']}mm, Y={box['y']}mm, Z={box['z']}mm"
            )
            self.new_x_var.set(str(int(box["x"])))
            self.new_y_var.set(str(int(box["y"])))
            self.new_z_var.set(str(int(box["z"])))
        else:
            # LỌC INDEX HỢP LỆ TRƯỚC
            valid_indices = [
                idx for idx in self.selected_item_indices
                if 0 <= idx < len(layer["boxes"])
            ]

            # Nếu không còn item hợp lệ → Clear selection
            if not valid_indices:
                self.selected_item_indices = []
                self.selected_item_label.config(text="Không có")
                self.new_x_var.set("")
                self.new_y_var.set("")
                self.new_z_var.set("")
                return

            self.selected_item_indices = valid_indices
            self.selected_item_label.config(
                text=f"{len(self.selected_item_indices)} items được chọn"
            )

            avg_x = sum(
                layer["boxes"][idx]["x"]
                for idx in self.selected_item_indices
            ) / len(self.selected_item_indices)

            avg_y = sum(
                layer["boxes"][idx]["y"]
                for idx in self.selected_item_indices
            ) / len(self.selected_item_indices)

            avg_z = sum(
                layer["boxes"][idx]["z"]
                for idx in self.selected_item_indices
            ) / len(self.selected_item_indices)

            self.new_x_var.set(str(int(avg_x)))
            self.new_y_var.set(str(int(avg_y)))
            self.new_z_var.set(str(int(avg_z)))

    
    # =============================================================
    # MATH EXPRESSION EVAL FOR 3D MOVE
    # =============================================================
    def _eval_math_expr(self, expr):
        """Tính biểu thức toán học đơn giản (+ - * / ( )) và trả về số nguyên"""
        if expr is None:
            raise ValueError("Empty")
        expr = str(expr).strip()
        if not expr:
            raise ValueError("Empty")

        # Bỏ khoảng trắng
        expr = expr.replace(" ", "")

        # Chỉ cho phép các ký tự sau
        allowed = "0123456789+-*/()."
        for ch in expr:
            if ch not in allowed:
                raise ValueError("Invalid char")

        # Đánh giá biểu thức một cách an toàn
        value = eval(expr, {"__builtins__": None}, {})
        return int(round(float(value)))

    def get_selected_axis_value(self, axis):
        """Lấy giá trị X/Y/Z hiện tại của item đầu tiên đang chọn"""
        if not getattr(self, 'selected_item_indices', None):
            return 0

        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        if container_idx < 0 or layer_idx < 0:
            return 0

        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        if not self.selected_item_indices:
            return 0

        idx = self.selected_item_indices[0]
        if idx < 0 or idx >= len(layer["boxes"]):
            return 0

        box = layer["boxes"][idx]
        return box[axis]


    
    def move_to_exact_position_3d(self, x=None, y=None, z=None, axis=None):
        """Di chuyển item 3D đến vị trí tuyệt đối, hỗ trợ nhập biểu thức như 523+27"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất một item trước!")
            return

        # Lưu trạng thái để UNDO
        self.save_current_state_for_undo_3d()

        try:
            # Trường hợp điều khiển từng trục qua ô nhập
            if axis == 'x':
                new_x = self._eval_math_expr(self.new_x_var.get())
                self.new_x_var.set(str(new_x))
                dx = new_x - self.get_selected_axis_value('x')
                self.move_selected_items_3d(dx, 0, 0)
                return

            if axis == 'y':
                new_y = self._eval_math_expr(self.new_y_var.get())
                self.new_y_var.set(str(new_y))
                dy = new_y - self.get_selected_axis_value('y')
                self.move_selected_items_3d(0, dy, 0)
                return

            if axis == 'z':
                new_z = self._eval_math_expr(self.new_z_var.get())
                self.new_z_var.set(str(new_z))
                dz = new_z - self.get_selected_axis_value('z')
                self.move_selected_items_3d(0, 0, dz)
                return

            # Trường hợp truyền trực tiếp x, y, z hoặc dùng cả 3 ô
            if x is None:
                x = self._eval_math_expr(self.new_x_var.get())
                self.new_x_var.set(str(x))
            if y is None:
                y = self._eval_math_expr(self.new_y_var.get())
                self.new_y_var.set(str(y))
            if z is None:
                z = self._eval_math_expr(self.new_z_var.get())
                self.new_z_var.set(str(z))

            dx = x - self.get_selected_axis_value('x')
            dy = y - self.get_selected_axis_value('y')
            dz = z - self.get_selected_axis_value('z')
            self.move_selected_items_3d(dx, dy, dz)

        except Exception:
            messagebox.showerror(
                "Lỗi",
                "Biểu thức không hợp lệ!\n"
                "Hãy nhập các phép toán như 523+27, 1000-250, (200+40)*2 ..."
            )

    def move_selected_items_3d(self, delta_x, delta_y, delta_z):
        """Move selected items by delta_x, delta_y, delta_z in 3D"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất một item trước!")
            return
            
        self.save_current_state_for_undo_3d()
            
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()
        
        for idx in self.selected_item_indices:
            box = layer["boxes"][idx]
            
            new_x = box["x"] + delta_x
            new_y = box["y"] + delta_y
            new_z = box["z"] + delta_z
            
            new_x = max(0, min(new_x, cL - box["L"]))
            new_y = max(0, min(new_y, cW - box["W"]))
            new_z = max(0, min(new_z, cH - box["H"]))
            
            box["x"] = new_x
            box["y"] = new_y
            box["z"] = new_z
        
        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def align_right_3d(self):
        """Align selected items to right in 3D"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất một item trước!")
            return
            
        self.save_current_state_for_undo_3d()
            
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cL = self.container_length.get()
        
        for idx in self.selected_item_indices:
            box = layer["boxes"][idx]
            new_x = cL - box["L"]
            box["x"] = new_x
        
        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def align_bottom_3d(self):
        """Align selected items to bottom in 3D"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất một item trước!")
            return
            
        self.save_current_state_for_undo_3d()
            
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cW = self.container_width.get()
        
        for idx in self.selected_item_indices:
            box = layer["boxes"][idx]
            new_y = cW - box["W"]
            box["y"] = new_y
        
        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def align_top_3d(self):
        """Align selected items to top in 3D"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất một item trước!")
            return
            
        self.save_current_state_for_undo_3d()
            
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        cH = self.container_height.get()
        
        for idx in self.selected_item_indices:
            box = layer["boxes"][idx]
            new_z = cH - box["H"]
            box["z"] = new_z
        
        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def select_all_items_3d(self):
        """Select all items in layer for 3D movement"""
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        
        self.selected_item_indices = list(range(len(layer["boxes"])))
        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def deselect_all_items_3d(self):
        """Deselect all items for 3D movement"""
        self.selected_item_indices = []
        self.update_selection_info_3d()
        self.draw_move_view_3d()

    def auto_rearrange_3d(self):
        """Automatically rearrange items in 3D"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất một item trước!")
            return
            
        self.save_current_state_for_undo_3d()
            
        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        
        if container_idx < 0 or layer_idx < 0:
            return
            
        container = self.result[container_idx]
        layer = container["layers"][layer_idx]
        
        # Sort by volume (largest first)
        boxes_sorted = sorted(layer["boxes"], key=lambda x: x["L"] * x["W"] * x["H"], reverse=True)
        
        # Simple 3D packing algorithm
        current_x = 0
        current_y = 0
        current_z = 0
        max_length_in_row = 0
        max_width_in_column = 0
        
        for box in boxes_sorted:
            if current_x + box["L"] > self.container_length.get():
                current_x = 0
                current_y += max_width_in_column
                max_width_in_column = 0
                
                if current_y + box["W"] > self.container_width.get():
                    current_y = 0
                    current_z += box["H"]  # Start new layer
                    max_width_in_column = 0
            
            if current_y + box["W"] > self.container_width.get():
                current_y = 0
                current_z += box["H"]
                max_width_in_column = 0
            
            if current_z + box["H"] > self.container_height.get():
                break
            
            box["x"] = current_x
            box["y"] = current_y
            box["z"] = current_z
            
            current_x += box["L"]
            max_length_in_row = max(max_length_in_row, box["L"])
            max_width_in_column = max(max_width_in_column, box["W"])
        
        self.selected_item_indices = []
        self.draw_move_view_3d()
        messagebox.showinfo("Thành công", "Đã tự động sắp xếp lại các items trong không gian 3D!")

    def reset_move_positions_3d(self):
        """Reset item positions to original algorithm positions in 3D"""
        if messagebox.askyesno("Xác nhận", "Bạn có chắc muốn reset tất cả vị trí về trạng thái ban đầu?"):
            container_idx = self.move_cb_container.current()
            layer_idx = self.move_cb_layer.current()
            
            if container_idx < 0 or layer_idx < 0:
                return
                
            current_container = self.result[container_idx]
            current_layer_name = self.move_cb_layer.get()
            
            # Get all items from the container
            raw_items = []
            for layer in current_container["layers"]:
                for box in layer["boxes"]:
                    raw_items.append({
                        "L": box["L"], "W": box["W"], "H": box["H"], 
                        "NoID": box["NoID"], "uid": box["uid"],
                        "rotate": 1
                    })
            
            cL = self.container_length.get()
            cW = self.container_width.get()
            cH = self.container_height.get()
            
            # Re-run packing algorithm
            new_container = self.pack_gap_filling_single_container(raw_items, cL, cW, cH)
            
            if new_container:
                packed, layers = new_container
                
                # Find and update the current layer
                for new_layer in layers:
                    if new_layer["name"] == current_layer_name:
                        # Update boxes in current layer
                        current_container["layers"][layer_idx]["boxes"] = new_layer["boxes"]
                        
                        # Also update Z positions to match original algorithm
                        for box in current_container["layers"][layer_idx]["boxes"]:
                            box["z"] = new_layer["z"]
                        break
                
                self.selected_item_indices = []
                self.update_selection_info_3d()
                self.draw_move_view_3d()
                messagebox.showinfo("Thành công", "Đã reset vị trí các item về vị trí tối ưu!")

    def rotate_selected_items_90(self):
        """Rotate selected item(s) 90 degrees (swap W <-> H)"""
        if not self.selected_item_indices:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn ít nhất 1 item để xoay!")
            return

        self.save_current_state_for_undo_3d()

        container_idx = self.move_cb_container.current()
        layer_idx = self.move_cb_layer.current()
        if container_idx < 0 or layer_idx < 0:
            return

        container = self.result[container_idx]
        layer = container["layers"][layer_idx]

        for idx in list(self.selected_item_indices):
            if 0 <= idx < len(layer["boxes"]):
                box = layer["boxes"][idx]
                box["W"], box["H"] = box["H"], box["W"]
                box["rotated"] = not box.get("rotated", False)

        self.update_selection_info_3d()
        self.draw_move_view_3d()

    # =============================================================
    # UNDO/REDO FUNCTIONS
    # =============================================================
    
    
    def save_current_state_for_undo_3d(self):
        """Lưu TOÀN BỘ trạng thái container để Undo cả chuyển layer"""
        import json
        snapshot = json.loads(json.dumps(self.result))
        self.undo_stack.append(snapshot)

        if len(self.undo_stack) > self.max_undo_steps:
            self.undo_stack.pop(0)

        self.redo_stack.clear()


    
    def undo_move_3d(self):
        if not self.undo_stack:
            return
        import json
        prev_state = self.undo_stack.pop()
        # đẩy trạng thái hiện tại sang redo
        self.redo_stack.append(json.loads(json.dumps(self.result)))
        # khôi phục
        self.result = json.loads(json.dumps(prev_state))
        self.draw_move_view_3d()
        self.draw_source_views()
        self.update_selection_info_3d()


    
    def redo_move_3d(self):
        if not self.redo_stack:
            return
        import json
        next_state = self.redo_stack.pop()
        # đẩy lại undo
        self.undo_stack.append(json.loads(json.dumps(self.result)))
        # phục hồi
        self.result = json.loads(json.dumps(next_state))
        self.draw_move_view_3d()
        self.draw_source_views()
        self.update_selection_info_3d()


    def save_moved_items_3d(self, window):
        """Lưu thay đổi 3D và cập nhật lại toàn bộ thông tin container"""
        if not self.result:
            
            return

        try:
            for container in self.result:
                layers = container.get("layers", [])
                all_boxes = []

                # Cập nhật chiều cao từng layer + gom toàn bộ box
                for layer in layers:
                    boxes = layer.get("boxes", [])
                    if boxes:
                        max_height = max(float(b.get("H", 0) or 0) for b in boxes)
                        layer["height"] = max_height
                    else:
                        layer["height"] = 0
                    all_boxes.extend(boxes)

                # Cập nhật lại tổng số kiện và thể tích của container
                container["packed_count"] = len(all_boxes)
                container["packed_vol"] = sum(
                    float(b.get("L", 0) or 0)
                    * float(b.get("W", 0) or 0)
                    * float(b.get("H", 0) or 0)
                    for b in all_boxes
                )

        except Exception as e:
            messagebox.showwarning(
                "Cảnh báo",
                f"Có lỗi khi cập nhật lại thông tin container:\n{e}\n"
                "Dữ liệu xếp kiện vẫn được giữ nguyên."
            )

        # Cập nhật lại phần kết quả và các mô hình 2D
        self.display_advanced_results()
        self.update_visualizer_controls()
        self.update_full_visualizer_controls()
        self.draw_cross_sections()
        
        # Cập nhật Tab 2
        if hasattr(self, 'tab2_cross_container'):
            self.update_tab2_controls()

        messagebox.showinfo(
            "Thành công",
            "ĐÃ LƯU TẤT CẢ THAY ĐỔI!\n"
            "✓ Vị trí items 3D\n"
            "✓ Items chuyển giữa containers\n"
            "✓ Thông tin container đã được cập nhật"
        )
    
    def update_tab2_controls(self):
        """Cập nhật các điều khiển trong Tab 2"""
        if not self.result:
            return
            
        # Cập nhật combobox trong Tab 2
        container_names = [c["name"] for c in self.result]
        self.tab2_cross_container['values'] = container_names
        self.tab2_top_container['values'] = container_names
        
        if container_names:
            self.tab2_cross_container.current(0)
            self.tab2_top_container.current(0)
            self.update_tab2_top_layers()
            self.draw_tab2_cross_sections()
            self.draw_tab2_topview()

    # =============================================================
    # LAYER REORDERING FUNCTIONS
    # =============================================================
    
    def reorder_layers(self):
        """Open window to reorder layers"""
        if not self.result:
            messagebox.showwarning("Cảnh báo", "Chưa có kết quả tính toán! Hãy chạy tính toán xếp kiện trước.")
            return
        
        reorder_window = tk.Toplevel(self.root)
        reorder_window.title("Sắp xếp lại thứ tự các lớp")
        reorder_window.geometry("600x500")
        reorder_window.transient(self.root)
        reorder_window.grab_set()
        
        container_frame = ttk.Frame(reorder_window)
        container_frame.pack(fill="x", padx=10, pady=10)
        
        ttk.Label(container_frame, text="Chọn xe:").pack(side="left", padx=2)
        self.reorder_cb_container = ttk.Combobox(container_frame, state="readonly", width=20)
        self.reorder_cb_container.pack(side="left", padx=2)
        self.reorder_cb_container['values'] = [c["name"] for c in self.result]
        self.reorder_cb_container.current(0)
        self.reorder_cb_container.bind("<<ComboboxSelected>>", lambda e: self.update_reorder_list())
        
        list_frame = ttk.LabelFrame(reorder_window, text="Danh sách lớp (kéo thả để sắp xếp lại)")
        list_frame.pack(fill="both", expand=True, padx=10, pady=2)
        
        listbox_frame = ttk.Frame(list_frame)
        listbox_frame.pack(fill="both", expand=True, padx=2, pady=2)
        
        scrollbar = ttk.Scrollbar(listbox_frame)
        scrollbar.pack(side="right", fill="y")
        
        self.reorder_listbox = tk.Listbox(listbox_frame, yscrollcommand=scrollbar.set, font=("Consolas", 10), 
                                         selectmode=tk.SINGLE, height=15)
        self.reorder_listbox.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=self.reorder_listbox.yview)
        
        self.setup_drag_drop(self.reorder_listbox)
        
        control_frame = ttk.Frame(reorder_window)
        control_frame.pack(fill="x", padx=10, pady=10)
        
        ttk.Button(control_frame, text="Lên trên", command=lambda: self.move_layer_up()).pack(side="left", padx=2)
        ttk.Button(control_frame, text="Xuống dưới", command=lambda: self.move_layer_down()).pack(side="left", padx=2)
        ttk.Button(control_frame, text="Đặt lại thứ tự Z", command=lambda: self.reset_layer_order_by_z()).pack(side="left", padx=2)
        ttk.Button(control_frame, text="Áp dụng và chạy lại", command=lambda: self.apply_new_layer_order(reorder_window)).pack(side="right", padx=2)
        ttk.Button(control_frame, text="Hủy", command=reorder_window.destroy).pack(side="right", padx=2)
        
        self.update_reorder_list()

    def setup_drag_drop(self, listbox):
        """Setup drag and drop for Listbox"""
        def on_drag_start(event):
            widget = event.widget
            index = widget.nearest(event.y)
            widget._drag_start_index = index
            widget.selection_clear(0, tk.END)
            widget.selection_set(index)
        
        def on_drag_motion(event):
            widget = event.widget
            index = widget.nearest(event.y)
            if hasattr(widget, '_drag_start_index') and widget._drag_start_index != index:
                items = list(widget.get(0, tk.END))
                item = items.pop(widget._drag_start_index)
                items.insert(index, item)
                
                widget.delete(0, tk.END)
                for item in items:
                    widget.insert(tk.END, item)
                
                widget._drag_start_index = index
                widget.selection_clear(0, tk.END)
                widget.selection_set(index)
        
        listbox.bind('<Button-1>', on_drag_start)
        listbox.bind('<B1-Motion>', on_drag_motion)

    def update_reorder_list(self):
        """Update layer list in reorder window - Zn ở trên cùng, Z1 ở dưới cùng"""
        if not hasattr(self, 'reorder_listbox'):
            return
            
        container_idx = self.reorder_cb_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        self.reorder_listbox.delete(0, tk.END)
        
        # Sắp xếp theo Z giảm dần (Zn ở trên cùng, Z1 ở dưới cùng)
        layers_sorted = sorted(container["layers"], key=lambda x: x["z"], reverse=True)
        
        for layer in layers_sorted:
            area = sum(box["L"] * box["W"] for box in layer["boxes"])
            layer_info = f"{layer['name']} | Z={layer['z']}mm | Cao: {layer['height']}mm | Diện tích: {area:,.0f}mm² | {len(layer['boxes'])} kiện"
            self.reorder_listbox.insert(tk.END, layer_info)

    def move_layer_up(self):
        """Move layer up in list"""
        selected = self.reorder_listbox.curselection()
        if not selected:
            return
            
        idx = selected[0]
        if idx == 0:
            return
            
        item = self.reorder_listbox.get(idx)
        self.reorder_listbox.delete(idx)
        self.reorder_listbox.insert(idx - 1, item)
        self.reorder_listbox.selection_set(idx - 1)

    def move_layer_down(self):
        """Move layer down in list"""
        selected = self.reorder_listbox.curselection()
        if not selected:
            return
            
        idx = selected[0]
        if idx == self.reorder_listbox.size() - 1:
            return
            
        item = self.reorder_listbox.get(idx)
        self.reorder_listbox.delete(idx)
        self.reorder_listbox.insert(idx + 1, item)
        self.reorder_listbox.selection_set(idx + 1)

    def reset_layer_order_by_z(self):
        """Reset layer order by Z coordinate (Zn ở trên cùng, Z1 ở dưới cùng)"""
        container_idx = self.reorder_cb_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        
        # Sắp xếp theo Z giảm dần (Zn ở trên cùng, Z1 ở dưới cùng)
        layers_sorted = sorted(container["layers"], key=lambda x: x["z"], reverse=True)
        
        self.reorder_listbox.delete(0, tk.END)
        for layer in layers_sorted:
            area = sum(box["L"] * box["W"] for box in layer["boxes"])
            layer_info = f"{layer['name']} | Z={layer['z']}mm | Cao: {layer['height']}mm | Diện tích: {area:,.0f}mm² | {len(layer['boxes'])} kiện"
            self.reorder_listbox.insert(tk.END, layer_info)

    def apply_new_layer_order(self, window):
        """Apply new layer order (Zn ở trên cùng trong list nhưng Z1 vẫn ở đáy container)"""
        container_idx = self.reorder_cb_container.current()
        if container_idx < 0:
            return
            
        container = self.result[container_idx]
        
        # Lấy thứ tự mới từ listbox (Zn ở trên cùng trong list)
        new_order = []
        for i in range(self.reorder_listbox.size()):
            layer_info = self.reorder_listbox.get(i)
            for layer in container["layers"]:
                area = sum(box["L"] * box["W"] for box in layer["boxes"])
                expected_info = f"{layer['name']} | Z={layer['z']}mm | Cao: {layer['height']}mm | Diện tích: {area:,.0f}mm² | {len(layer['boxes'])} kiện"
                if layer_info == expected_info:
                    new_order.append(layer)
                    break
        
        # Đảo ngược để Z1 ở đáy container (vị trí Z=0)
        new_order.reverse()
        
        total_height = sum(layer["height"] for layer in new_order)
        container_height = self.container_height.get()
        
        if total_height > container_height:
            messagebox.showwarning("Cảnh báo", 
                                 f"Tổng chiều cao các lớp ({total_height}mm) vượt quá chiều cao container ({container_height}mm)!")
            return
        
        container["layers"] = new_order
        
        # Tính toán lại tọa độ Z (Z1 ở đáy = 0)
        current_z = 0
        for i, layer in enumerate(container["layers"]):
            layer["z"] = current_z
            layer["name"] = f"Lớp Z{i+1}"
            for box in layer["boxes"]:
                box["z"] = current_z
            current_z += layer["height"]
        
        self.display_advanced_results()
        self.update_visualizer_controls()
        self.update_full_visualizer_controls()
        self.draw_cross_sections()
        
        # Cập nhật Tab 2
        if hasattr(self, 'tab2_cross_container'):
            self.draw_tab2_cross_sections()
            self.draw_tab2_topview()
        
        messagebox.showinfo("Thành công", "Đã áp dụng thứ tự lớp mới!")

    # =============================================================
    # PACKING ALGORITHMS - IMPROVED STACKING (2D PACKING ON BASE SURFACE)
    # =============================================================
    
    def run_advanced_optimization(self):
        raw_items = []
        for child in self.data_tree.get_children():
            v = self.data_tree.item(child)["values"]
            try:
                L, W, H, Q, ID = int(v[0]), int(v[1]), int(v[2]), int(v[3]), str(v[4])
                rotate = 1
                if len(v) >= 6:
                    rotate_str = str(v[5]).strip().lower()
                    if rotate_str in ['0', 'false', 'no', 'không']:
                        rotate = 0
                    else:
                        rotate = 1
                
                for _ in range(Q):
                    raw_items.append({
                        "L": L, "W": W, "H": H, 
                        "NoID": ID, "uid": random.random(),
                        "rotate": rotate
                    })
            except (ValueError, IndexError):
                pass
            
        if not raw_items: 
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu hàng hóa!")
            return

        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()

        invalid_items = []
        for item in raw_items:
            fits = False
            allow_rotate = item["rotate"] == 1 and self.allow_rotation.get()
            
            if allow_rotate:
                fits = (
                    (item["L"] <= cL and item["W"] <= cW and item["H"] <= cH) or
                    (item["L"] <= cL and item["H"] <= cW and item["W"] <= cH) or
                    (item["W"] <= cL and item["L"] <= cW and item["H"] <= cH) or
                    (item["W"] <= cL and item["H"] <= cW and item["L"] <= cH) or
                    (item["H"] <= cL and item["L"] <= cW and item["W"] <= cH) or
                    (item["H"] <= cL and item["W"] <= cW and item["L"] <= cH)
                )
            else:
                fits = (item["L"] <= cL and item["W"] <= cW and item["H"] <= cH)
            
            if not fits:
                rotate_status = "Có thể xoay" if allow_rotate else "Không xoay"
                invalid_items.append(f"{item['NoID']} ({item['L']}x{item['W']}x{item['H']}) - {rotate_status}")
        
        if invalid_items:
            messagebox.showerror("Lỗi", f"Các hàng sau quá khổ container:\n" + "\n".join(invalid_items[:5]) + 
                               ("\n..." if len(invalid_items) > 5 else ""))
            return

        if self.multi_strategy.get():
            best_solution = self.run_multi_strategy_optimization(raw_items, cL, cW, cH)
        else:
            best_solution = self.run_single_strategy_optimization(raw_items, cL, cW, cH)
            
        if not best_solution:
            messagebox.showerror("Lỗi", "Không thể xếp hàng vào container!")
            return
            
        self.result = best_solution
        
        self.rotation_analysis = self.analyze_rotation_improvement(raw_items, cL, cW, cH)
        
        self.display_advanced_results()
        self.update_visualizer_controls()
        self.update_full_visualizer_controls()
        self.draw_cross_sections()
        
        # Cập nhật Tab 2
        if hasattr(self, 'tab2_cross_container'):
            self.update_tab2_controls()

    def run_multi_strategy_optimization(self, raw_items, cL, cW, cH):
        strategies = [
            {"name": "GFBUp", "func": self.pack_gap_filling},
            {"name": "GFI", "func": self.pack_gap_filling_interleaved},
            {"name": "Greedy + Layer-based", "func": self.pack_greedy_layer_based},
            {"name": "Hybrid Approach", "func": self.pack_hybrid_approach}
        ]
        
        best_solution = None
        best_metric = float('-inf')
        best_strategy_name = ""
        
        for strategy in strategies:
            try:
                start_time = time.time()
                solution = strategy["func"](raw_items[:], cL, cW, cH)
                end_time = time.time()
                
                if solution and len(solution) > 0:
                    metric = self.evaluate_solution_quality(solution, cL, cW, cH)
                    
                    for i, container in enumerate(solution):
                        container["strategy"] = strategy["name"]
                        container["time"] = end_time - start_time
                        container["name"] = f"Xe {i+1:02d}"
                    
                    print(f"Chiến lược {strategy['name']}: {len(solution)} xe, Điểm: {metric:.2f}, Thời gian: {end_time - start_time:.2f}s")
                    
                    if metric > best_metric:
                        best_metric = metric
                        best_solution = solution
                        best_strategy_name = strategy["name"]
            except Exception as e:
                print(f"Lỗi với chiến lược {strategy['name']}: {str(e)}")
                continue
        
        if best_solution:
            print(f"CHIẾN LƯỢC TỐT NHẤT: {best_strategy_name} với điểm số: {best_metric:.2f}")
            for container in best_solution:
                container["best_strategy"] = best_strategy_name
                
        return best_solution

    def run_single_strategy_optimization(self, raw_items, cL, cW, cH):
        solution = self.pack_gap_filling(raw_items, cL, cW, cH)
        if solution:
            for i, container in enumerate(solution):
                container["name"] = f"Xe {i+1:02d}"
        return solution

    def evaluate_solution_quality(self, solution, cL, cW, cH):
        if not solution:
            return float('-inf')
            
        total_volume = cL * cW * cH * len(solution)
        used_volume = sum(cont["packed_vol"] for cont in solution)
        
        volume_utilization = used_volume / total_volume if total_volume > 0 else 0
        container_count = len(solution)
        
        item_counts = [cont["packed_count"] for cont in solution]
        stability = 1 - (max(item_counts) - min(item_counts)) / max(item_counts) if max(item_counts) > 0 else 1
        
        metric = (volume_utilization * 0.5 + 
                 (1 / container_count) * 0.3 + 
                 stability * 0.2)
        
        return metric

    def pack_gap_filling(self, items, cL, cW, cH):
        if self.group_similar.get():
            items = self.normalize_dimensions_advanced(items)
        
        remaining_items = items[:]
        all_containers = []
        container_count = 0
        
        while remaining_items and container_count < 100:
            container_count += 1
            
            packed, layers = self.pack_gap_filling_single_container(remaining_items, cL, cW, cH)
            
            if not packed:
                break
            
            container = {
                "name": f"Xe {container_count:02d}",
                "layers": layers,
                "packed_count": len(packed),
                "packed_vol": sum(i["L"]*i["W"]*i["H"] for i in packed)
            }
            
            self.sort_layers_by_z(container)
            all_containers.append(container)
            
            packed_uids = [item["uid"] for item in packed]
            remaining_items = [item for item in remaining_items if item["uid"] not in packed_uids]
            
        return all_containers

    def pack_gap_filling_single_container(self, items, cL, cW, cH):
        if self.group_similar.get():
            items = self.normalize_dimensions_simple(items)

        rem = items[:]
        layers = []
        packed_total = []

        current_z = 0
        max_layers = 200
        layer_count = 0

        while rem and current_z < cH and layer_count < max_layers:
            layer_height = self.select_layer_height_interleaved(rem, cH - current_z)
            if layer_height is None:
                break

            placed_in_layer = self.build_layer_by_length_skyline(rem, cL, cW, layer_height, current_z)
            if not placed_in_layer:
                possible_heights = sorted({it["H"] for it in rem if it["H"] <= (cH-current_z)})
                smaller = [h for h in possible_heights if h < layer_height]
                if smaller:
                    layer_height = max(smaller)
                    placed_in_layer = self.build_layer_by_length_skyline(rem, cL, cW, layer_height, current_z)
                if not placed_in_layer:
                    break

            layers.append({
                "name": f"Layer_{layer_count+1}",
                "z": current_z,
                "height": layer_height,
                "boxes": placed_in_layer
            })

            packed_total.extend(placed_in_layer)
            placed_uids = set(b["uid"] for b in placed_in_layer)
            rem = [r for r in rem if r["uid"] not in placed_uids]

            current_z += layer_height
            layer_count += 1

        return packed_total, layers

    def normalize_dimensions_simple(self, items, tolerance=5):
        if not items:
            return items
        groups = []
        normalized = []
        for it in items:
            matched = False
            for g in groups:
                if it["NoID"] == g["NoID"] and abs(it["L"]-g["L"])<=tolerance and abs(it["W"]-g["W"])<=tolerance and abs(it["H"]-g["H"])<=tolerance:
                    matched = True
                    normalized.append({"L": g["L"], "W": g["W"], "H": g["H"], "NoID": it["NoID"], "uid": it["uid"], "rotate": it["rotate"]})
                    break
            if not matched:
                groups.append({"L": it["L"], "W": it["W"], "H": it["H"], "NoID": it["NoID"]})
                normalized.append(it.copy())
        return normalized

    def select_layer_height_interleaved(self, items, remaining_height):
        heights = sorted([it["H"] for it in items if it["H"] <= remaining_height])
        if not heights:
            return None
        
        n = len(heights)
        p30 = heights[max(0, int(n*0.7)-1)]
        tall = [h for h in heights if h >= p30]
        short = [h for h in heights if h <= heights[max(0, int(n*0.3)-1)]]

        height_counts = Counter(heights)
        mode_height = height_counts.most_common(1)[0][0]
        
        if len(tall) > len(short):
            chosen = min(tall)
        elif len(short) > len(tall):
            chosen = max(short)
        else:
            chosen = mode_height

        if chosen > remaining_height:
            chosen = remaining_height
        return chosen

    # =============================================================
    # CẢI TIẾN CHÍNH: ƯU TIÊN ITEM CÓ CHIỀU CAO CHÊNH NHAU ≤ tolerance mm CÙNG LAYER
    # (ĐÃ THAY ĐỔI TỪ 10mm CỐ ĐỊNH SANG GIÁ TRỊ TỪ BIẾN self.height_tolerance_var)
    # =============================================================
    
    def build_layer_by_length_skyline(self, items, cL, cW, layer_height, current_z):
        """Xây dựng layer với cải tiến cho phép item có chiều cao chênh nhau ≤ tolerance mm"""
        candidates = []
        for it in items:
            if self.can_item_fit_in_layer_with_tolerance(it, cL, cW, layer_height):
                candidates.append(it.copy())

        if not candidates:
            return []

        candidates.sort(key=lambda x: (x["L"]*x["W"], x["H"]), reverse=True)

        placed = []
        rows = []
        
        # Tìm chiều cao thực tế của layer (có thể lớn hơn layer_height nếu có item cao hơn)
        actual_layer_height = layer_height
        
        for it in candidates:
            # Tạo các biến thể item với tolerance cho phép
            item_variants = self.generate_item_variants_with_tolerance(it, cL, cW, layer_height)
            
            placed_flag = False
            for variant in item_variants:
                if variant["L"] > cL or variant["W"] > cW or variant["H"] > (layer_height + self.height_tolerance_var.get()):
                    continue

                # Cập nhật actual_layer_height nếu item cao hơn layer_height ban đầu
                if variant["H"] > actual_layer_height:
                    actual_layer_height = variant["H"]

                for row in rows:
                    if variant["W"] <= row["height"]:
                        segs = row["segments"]
                        x_pos = self.find_x_position_in_segments(segs, variant["L"], cL)
                        if x_pos is not None:
                            box = {
                                "x": x_pos, "y": row["y"], "z": current_z, 
                                "L": variant["L"], "W": variant["W"], "H": variant["H"], 
                                "NoID": variant["NoID"], "uid": variant["uid"],
                                "rotated": variant.get("rotated", False),
                                "stacked": False,
                                "stack_level": 1
                            }
                            placed.append(box)
                            row["segments"] = self.update_segments_after_place(segs, x_pos, variant["L"])
                            placed_flag = True
                            break
                if placed_flag:
                    break

                next_y = sum(r["height"] for r in rows)
                if next_y + variant["W"] <= cW:
                    box = {
                        "x": 0, "y": next_y, "z": current_z, 
                        "L": variant["L"], "W": variant["W"], "H": variant["H"], 
                        "NoID": variant["NoID"], "uid": variant["uid"],
                        "rotated": variant.get("rotated", False),
                        "stacked": False,
                        "stack_level": 1
                    }
                    placed.append(box)
                    rows.append({"y": next_y, "height": variant["W"], "segments": [(variant["L"], cL)]})
                    placed_flag = True
                    break

        if not placed:
            return []

        placed_uids = set(b["uid"] for b in placed)
        remaining_small = [it for it in items if it["uid"] not in placed_uids]

        # Sử dụng chiến lược chồng mới với tính toán tolerance
        if self.allow_stacking_in_layer.get():
            remaining_small = self.place_stacked_items_with_tolerance(placed, rows, remaining_small, cL, cW, actual_layer_height, current_z)
            # Cập nhật remaining_small: loại bỏ các item đã được đặt (có trong placed)
            placed_uids = set(b["uid"] for b in placed)
            remaining_small = [it for it in remaining_small if it["uid"] not in placed_uids]

        # Loại bỏ trùng lặp
        unique = {}
        final = []
        for b in placed:
            if b["uid"] not in unique:
                unique[b["uid"]] = True
                final.append(b)

        return final

    def can_item_fit_in_layer_with_tolerance(self, item, cL, cW, layer_height):
        """Kiểm tra item có thể fit vào layer với tolerance chiều cao"""
        if not self.allow_height_tolerance.get():
            # Nếu không bật tolerance, dùng logic cũ
            return self.can_item_fit_in_layer(item, cL, cW, layer_height)
        
        # Với tolerance, cho phép chiều cao lớn hơn đến tolerance mm
        tolerance_value = self.height_tolerance_var.get()
        max_allowed_height = layer_height + tolerance_value
        
        if item["L"] <= cL and item["W"] <= cW and item["H"] <= max_allowed_height:
            return True
        
        if self.allow_rotation.get() and item["rotate"] == 1:
            if item["L"] <= cL and item["H"] <= cW and item["W"] <= max_allowed_height:
                return True
            if item["W"] <= cL and item["L"] <= cW and item["H"] <= max_allowed_height:
                return True
            if item["H"] <= cL and item["L"] <= cW and item["W"] <= max_allowed_height:
                return True
            if item["W"] <= cL and item["H"] <= cW and item["L"] <= max_allowed_height:
                return True
            if item["H"] <= cL and item["W"] <= cW and item["L"] <= max_allowed_height:
                return True
        
        return False

    def generate_item_variants_with_tolerance(self, item, cL, cW, layer_height):
        """Tạo các biến thể item với tolerance chiều cao"""
        variants = []
        L, W, H = item["L"], item["W"], item["H"]
        
        # Sử dụng giá trị tolerance từ biến
        tolerance_value = self.height_tolerance_var.get() if self.allow_height_tolerance.get() else 0
        max_allowed_height = layer_height + tolerance_value
        
        if L <= cL and W <= cW and H <= max_allowed_height:
            variants.append({
                "L": L, "W": W, "H": H, 
                "NoID": item["NoID"], "uid": item["uid"],
                "rotated": False
            })
        
        if self.allow_rotation.get() and item["rotate"] == 1:
            if L <= cL and H <= cW and W <= max_allowed_height:
                variants.append({
                    "L": L, "W": H, "H": W, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if W <= cL and L <= cW and H <= max_allowed_height:
                variants.append({
                    "L": W, "W": L, "H": H, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if H <= cL and L <= cW and W <= max_allowed_height:
                variants.append({
                    "L": H, "W": L, "H": W, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if W <= cL and H <= cW and L <= max_allowed_height:
                variants.append({
                    "L": W, "W": H, "H": L, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if H <= cL and W <= cW and L <= max_allowed_height:
                variants.append({
                    "L": H, "W": W, "H": L, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
        
        variants.sort(key=lambda x: x["L"] * x["W"], reverse=True)
        
        return variants

    def place_stacked_items_with_tolerance(self, placed, rows, remaining_items, cL, cW, layer_height, current_z):
        """Đặt các item chồng với tolerance chiều cao"""
        strategy = self.stack_strategy.get()
        
        if strategy == "2d_packing":
            return self.place_stacked_items_2d_packing_with_tolerance(placed, rows, remaining_items, cL, cW, layer_height, current_z)
        elif strategy == "same_spot":
            return self.place_stacked_items_same_spot_with_tolerance(placed, rows, remaining_items, cL, cW, layer_height, current_z)
        else:  # "separate"
            return self.place_stacked_items_separate_with_tolerance(placed, rows, remaining_items, cL, cW, layer_height, current_z)

    def place_stacked_items_2d_packing_with_tolerance(self, placed, rows, remaining_items, cL, cW, layer_height, current_z):
        """Chiến lược 2D packing với tolerance chiều cao"""
        if not remaining_items:
            return remaining_items
            
        updated_remaining = remaining_items[:]
        
        # Tìm các base item có H_base < layer_height (có tính tolerance)
        base_items = [box for box in placed if box["H"] < layer_height]
        # Sắp xếp base từ lớn → nhỏ (ưu tiên base lớn để đặt nhiều item con)
        base_items.sort(key=lambda x: x["L"] * x["W"], reverse=True)

        for base in base_items:
            gap_h = layer_height - base["H"]
            if gap_h <= 0:
                continue

            # Lọc các item nhỏ chưa đặt, có thể xếp lên base này (có tính tolerance)
            candidate_small = [it for it in updated_remaining]
            
            if not candidate_small:
                continue

            # === Packing cục bộ 2D trên mặt base ===
            local_placed = []
            rows_local = []
            
            # Sắp xếp item nhỏ theo diện tích giảm dần
            candidates_for_base = []
            for s in candidate_small:
                variants = self.generate_item_variants_with_tolerance(s, 
                                                                    base["L"], base["W"], gap_h)
                for v in variants:
                    if v["L"] <= base["L"] and v["W"] <= base["W"] and v["H"] <= gap_h:
                        candidates_for_base.append({
                            "item": s,
                            "variant": v
                        })
                        break

            candidates_for_base.sort(key=lambda x: x["variant"]["L"] * x["variant"]["W"], reverse=True)

            stacked_uids = []
            
            for cand in candidates_for_base:
                s = cand["item"]
                v = cand["variant"]
                placed_flag = False

                # Thử đặt vào các row hiện có
                for row in rows_local:
                    if v["W"] <= row["height"]:
                        segs = row["segments"]
                        x_pos = self.find_x_position_in_segments(segs, v["L"], base["L"])
                        if x_pos is not None:
                            local_placed.append({
                                "x": x_pos,
                                "y": row["y"],
                                "h": v["H"],
                                "variant": v,
                                "uid": s["uid"]
                            })
                            row["segments"] = self.update_segments_after_place(segs, x_pos, v["L"])
                            placed_flag = True
                            stacked_uids.append(s["uid"])
                            break

                # Nếu không đặt được → tạo row mới
                if not placed_flag:
                    next_y = sum(r["height"] for r in rows_local)
                    if next_y + v["W"] <= base["W"]:
                        local_placed.append({
                            "x": 0,
                            "y": next_y,
                            "h": v["H"],
                            "variant": v,
                            "uid": s["uid"]
                        })
                        rows_local.append({
                            "y": next_y,
                            "height": v["W"],
                            "segments": self.update_segments_after_place([(0, base["L"])], 0, v["L"])
                        })
                        placed_flag = True
                        stacked_uids.append(s["uid"])

                if placed_flag:
                    # Đánh dấu đã dùng, không dùng cho base khác
                    updated_remaining = [r for r in updated_remaining if r["uid"] != s["uid"]]

            # === Sau khi packing cục bộ, gán tọa độ thực tế vào placed ===
            current_z_stack = base["z"] + base["H"]
            local_placed.sort(key=lambda b: (b["y"], b["x"]))

            for stacked_box_local in local_placed:
                v = stacked_box_local["variant"]
                s = None
                for cand in candidates_for_base:
                    if cand["item"]["uid"] == stacked_box_local["uid"]:
                        s = cand["item"]
                        break
                
                if s is None:
                    continue
                    
                stacked_box = {
                    "x": base["x"] + stacked_box_local["x"],
                    "y": base["y"] + stacked_box_local["y"],
                    "z": current_z_stack,
                    "L": v["L"],
                    "W": v["W"],
                    "H": v["H"],
                    "NoID": s["NoID"],
                    "uid": s["uid"],
                    "rotated": v.get("rotated", False),
                    "stacked": True,
                    "stack_level": 2
                }
                placed.append(stacked_box)
                current_z_stack += v["H"]
                if current_z_stack - (base["z"] + base["H"]) >= gap_h:
                    break

        return updated_remaining

    def place_stacked_items_same_spot_with_tolerance(self, placed, rows, remaining_items, cL, cW, layer_height, current_z):
        """Chiến lược same spot với tolerance chiều cao"""
        if not remaining_items:
            return remaining_items
            
        updated_remaining = remaining_items[:]
        base_items = [box for box in placed if box["H"] < layer_height]
        base_items.sort(key=lambda x: x["L"] * x["W"], reverse=True)
        
        stacked_uids = set()
        
        for base in base_items:
            gap_h = layer_height - base["H"]
            if gap_h <= 0:
                continue
                
            stackable_items = []
            for i, s in enumerate(updated_remaining):
                if s["uid"] in stacked_uids:
                    continue
                small_variants = self.generate_item_variants_with_tolerance(s, base["L"], base["W"], gap_h)
                
                for variant in small_variants:
                    if variant["L"] <= base["L"] and variant["W"] <= base["W"] and variant["H"] <= gap_h:
                        stackable_items.append({
                            "item": s,
                            "variant": variant,
                            "index": i,
                            "height": variant["H"]
                        })
                        break
            
            stackable_items.sort(key=lambda x: x["height"], reverse=True)
            
            best_stack = []
            best_height = 0
            
            # Tìm tổ hợp tốt nhất
            for i in range(len(stackable_items)):
                current_stack = []
                current_height = 0
                
                for j in range(i, len(stackable_items)):
                    s_item = stackable_items[j]
                    if current_height + s_item["height"] <= gap_h:
                        current_stack.append(s_item)
                        current_height += s_item["height"]
                        
                        if abs(current_height - gap_h) < 1:
                            break
                
                if current_height > best_height:
                    best_height = current_height
                    best_stack = current_stack.copy()
            
            # Đặt các item chồng lên cùng vị trí
            if best_stack:
                current_z_stack = current_z + base["H"]
                stack_level = 2
                for stack_item in best_stack:
                    variant = stack_item["variant"]
                    s = stack_item["item"]
                    
                    stacked_box = {
                        "x": base["x"],
                        "y": base["y"], 
                        "z": current_z_stack,
                        "L": variant["L"],
                        "W": variant["W"],
                        "H": variant["H"],
                        "NoID": s["NoID"],
                        "uid": s["uid"],
                        "rotated": variant.get("rotated", False),
                        "stacked": True,
                        "stack_level": stack_level
                    }
                    
                    placed.append(stacked_box)
                    stacked_uids.add(s["uid"])
                    current_z_stack += variant["H"]
                    stack_level += 1

        updated_remaining = [item for item in updated_remaining if item["uid"] not in stacked_uids]
        return updated_remaining

    def place_stacked_items_separate_with_tolerance(self, placed, rows, remaining_items, cL, cW, layer_height, current_z):
        """Chiến lược separate với tolerance chiều cao"""
        if not remaining_items:
            return remaining_items
            
        updated_remaining = remaining_items[:]
        
        stackable_areas = []
        for box in placed:
            if box["H"] < layer_height * 0.7:
                stackable_areas.append({
                    "base_box": box,
                    "remaining_height": layer_height - box["H"],
                    "used_height": 0
                })
        
        stackable_areas.sort(key=lambda x: (x["base_box"]["L"] * x["base_box"]["W"]), reverse=True)
        
        stacked_uids = set()
        
        for area in stackable_areas:
            if area["remaining_height"] <= 0 or not updated_remaining:
                continue
                
            base_box = area["base_box"]
            max_height = area["remaining_height"]
            
            stackable_candidates = []
            for i, item in enumerate(updated_remaining):
                if item["uid"] in stacked_uids:
                    continue
                variants = self.generate_item_variants_with_tolerance(item, base_box["L"], base_box["W"], max_height)
                for variant in variants:
                    if (variant["L"] <= base_box["L"] and 
                        variant["W"] <= base_box["W"] and 
                        variant["H"] <= max_height):
                        stackable_candidates.append({
                            "item": item,
                            "variant": variant,
                            "index": i
                        })
                        break
            
            if not stackable_candidates:
                continue
            
            stackable_candidates.sort(key=lambda x: x["variant"]["H"], reverse=True)
            
            for candidate in stackable_candidates:
                variant = candidate["variant"]
                item = candidate["item"]
                
                found_position = self.find_position_near_base(placed, rows, base_box, variant, cL, cW)
                
                if found_position:
                    stacked_box = {
                        "x": found_position["x"],
                        "y": found_position["y"], 
                        "z": current_z + base_box["H"],
                        "L": variant["L"],
                        "W": variant["W"],
                        "H": variant["H"],
                        "NoID": item["NoID"],
                        "uid": item["uid"],
                        "rotated": variant.get("rotated", False),
                        "stacked": True,
                        "stack_level": 2
                    }
                    
                    placed.append(stacked_box)
                    stacked_uids.add(item["uid"])
                    
                    self.update_rows_for_stacked_item(rows, stacked_box, cL)
                    
                    area["used_height"] += variant["H"]
                    area["remaining_height"] -= variant["H"]
                    
                    if area["remaining_height"] > 0:
                        for i2, item2 in enumerate(updated_remaining):
                            if item2["uid"] in stacked_uids:
                                continue
                            variants2 = self.generate_item_variants_with_tolerance(item2, variant["L"], variant["W"], area["remaining_height"])
                            for variant2 in variants2:
                                if (variant2["L"] <= variant["L"] and 
                                    variant2["W"] <= variant["W"] and 
                                    variant2["H"] <= area["remaining_height"]):
                                    
                                    stacked_box2 = {
                                        "x": found_position["x"],
                                        "y": found_position["y"], 
                                        "z": current_z + base_box["H"] + variant["H"],
                                        "L": variant2["L"],
                                        "W": variant2["W"],
                                        "H": variant2["H"],
                                        "NoID": item2["NoID"],
                                        "uid": item2["uid"],
                                        "rotated": variant2.get("rotated", False),
                                        "stacked": True,
                                        "stack_level": 3
                                    }
                                    
                                    placed.append(stacked_box2)
                                    stacked_uids.add(item2["uid"])
                                    break
                            break
                    
                    break

        updated_remaining = [item for item in updated_remaining if item["uid"] not in stacked_uids]
        return updated_remaining

    # Các hàm helper cần giữ lại
    def can_item_fit_in_layer(self, item, cL, cW, layer_height):
        """Hàm cũ để tương thích"""
        if item["L"] <= cL and item["W"] <= cW and item["H"] <= layer_height:
            return True
        
        if self.allow_rotation.get() and item["rotate"] == 1:
            if item["L"] <= cL and item["H"] <= cW and item["W"] <= layer_height:
                return True
            if item["W"] <= cL and item["L"] <= cW and item["H"] <= layer_height:
                return True
            if item["H"] <= cL and item["L"] <= cW and item["W"] <= layer_height:
                return True
            if item["W"] <= cL and item["H"] <= cW and item["L"] <= layer_height:
                return True
            if item["H"] <= cL and item["W"] <= cW and item["L"] <= layer_height:
                return True
        
        return False

    def generate_item_variants(self, item, cL, cW, layer_height):
        """Hàm cũ để tương thích"""
        variants = []
        L, W, H = item["L"], item["W"], item["H"]
        
        if L <= cL and W <= cW and H <= layer_height:
            variants.append({
                "L": L, "W": W, "H": H, 
                "NoID": item["NoID"], "uid": item["uid"],
                "rotated": False
            })
        
        if self.allow_rotation.get() and item["rotate"] == 1:
            if L <= cL and H <= cW and W <= layer_height:
                variants.append({
                    "L": L, "W": H, "H": W, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if W <= cL and L <= cW and H <= layer_height:
                variants.append({
                    "L": W, "W": L, "H": H, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if H <= cL and L <= cW and W <= layer_height:
                variants.append({
                    "L": H, "W": L, "H": W, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if W <= cL and H <= cW and L <= layer_height:
                variants.append({
                    "L": W, "W": H, "H": L, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
            
            if H <= cL and W <= cW and L <= layer_height:
                variants.append({
                    "L": H, "W": W, "H": L, 
                    "NoID": item["NoID"], "uid": item["uid"],
                    "rotated": True
                })
        
        variants.sort(key=lambda x: x["L"] * x["W"], reverse=True)
        
        return variants

    def find_position_near_base(self, placed, rows, base_box, variant, cL, cW):
        """Tìm vị trí trống gần base_box để đặt item chồng"""
        
        candidate_positions = [
            {"x": base_box["x"] + base_box["L"], "y": base_box["y"]},
            {"x": max(0, base_box["x"] - variant["L"]), "y": base_box["y"]},
            {"x": base_box["x"], "y": base_box["y"] + base_box["W"]},
            {"x": base_box["x"], "y": max(0, base_box["y"] - variant["W"])},
            {"x": base_box["x"] + base_box["L"], "y": base_box["y"] + base_box["W"]},
        ]
        
        for pos in candidate_positions:
            if (pos["x"] + variant["L"] <= cL and 
                pos["y"] + variant["W"] <= cW and
                pos["x"] >= 0 and pos["y"] >= 0):
                
                overlap = False
                test_rect = {
                    "x": pos["x"], 
                    "y": pos["y"], 
                    "L": variant["L"], 
                    "W": variant["W"]
                }
                
                for box in placed:
                    if self.boxes_overlap(test_rect, box):
                        overlap = True
                        break
                
                if not overlap:
                    return pos
        
        for row in rows:
            segs = row["segments"]
            x_pos = self.find_x_position_in_segments(segs, variant["L"], cL)
            if x_pos is not None:
                test_rect = {"x": x_pos, "y": row["y"], "L": variant["L"], "W": variant["W"]}
                if not self.boxes_overlap(test_rect, base_box):
                    return {"x": x_pos, "y": row["y"]}
        
        return None

    def boxes_overlap(self, rect1, rect2):
        """Kiểm tra hai hình chữ nhật có chồng lên nhau không"""
        return not (rect1["x"] + rect1["L"] <= rect2["x"] or
                    rect2["x"] + rect2["L"] <= rect1["x"] or
                    rect1["y"] + rect1["W"] <= rect2["y"] or
                    rect2["y"] + rect2["W"] <= rect1["y"])

    def update_rows_for_stacked_item(self, rows, stacked_box, cL):
        """Cập nhật rows khi đặt item chồng"""
        for row in rows:
            if row["y"] <= stacked_box["y"] < row["y"] + row["height"]:
                segs = row["segments"]
                row["segments"] = self.update_segments_after_place(segs, stacked_box["x"], stacked_box["L"])
                break
        else:
            rows.append({
                "y": stacked_box["y"],
                "height": stacked_box["W"],
                "segments": [(stacked_box["L"], cL)]
            })

    def find_x_position_in_segments(self, segments, length_needed, cL):
        for (start, end) in segments:
            if end - start >= length_needed:
                return start
        return None

    def update_segments_after_place(self, segments, x_pos, length):
        new = []
        for (s, e) in segments:
            if x_pos >= e or (x_pos + length) <= s:
                new.append((s, e))
            else:
                if s < x_pos:
                    new.append((s, x_pos))
                if x_pos + length < e:
                    new.append((x_pos + length, e))
        new.sort()
        merged = []
        for seg in new:
            if not merged:
                merged.append(seg)
            else:
                last = merged[-1]
                if last[1] >= seg[0]:
                    merged[-1] = (last[0], max(last[1], seg[1]))
                else:
                    merged.append(seg)
        return merged

    def pack_gap_filling_interleaved(self, items, cL, cW, cH):
        return self.pack_gap_filling(items, cL, cW, cH)

    def pack_greedy_layer_based(self, items, cL, cW, cH):
        return self.pack_gap_filling(items, cL, cW, cH)

    def pack_hybrid_approach(self, items, cL, cW, cH):
        return self.pack_gap_filling(items, cL, cW, cH)

    def normalize_dimensions_advanced(self, items, tolerance=5):
        if not self.group_similar.get():
            return items
            
        normalized = []
        dimension_groups = {}
        
        for item in items:
            found_group = None
            for group_key in dimension_groups:
                Lg, Wg, Hg, IDg, rotate_g = group_key
                
                size_match = (abs(item["L"] - Lg) <= tolerance and 
                             abs(item["W"] - Wg) <= tolerance and 
                             abs(item["H"] - Hg) <= tolerance)
                
                type_match = item["NoID"] == IDg
                rotate_match = item["rotate"] == rotate_g
                
                if size_match and type_match and rotate_match:
                    found_group = group_key
                    break
                    
                if item["rotate"] == 1:
                    permutations = [
                        (item["L"], item["W"], item["H"]),
                        (item["L"], item["H"], item["W"]),
                        (item["W"], item["L"], item["H"]),
                        (item["W"], item["H"], item["L"]),
                        (item["H"], item["L"], item["W"]),
                        (item["H"], item["W"], item["L"])
                    ]
                    
                    for perm in permutations:
                        if (abs(perm[0] - Lg) <= tolerance and 
                            abs(perm[1] - Wg) <= tolerance and 
                            abs(perm[2] - Hg) <= tolerance and
                            item["NoID"] == IDg and
                            item["rotate"] == rotate_g):
                            found_group = group_key
                            item["L"], item["W"], item["H"] = Lg, Wg, Hg
                            break
                        if found_group:
                            break
            
            if found_group:
                new_item = item.copy()
                new_item["L"] = dimension_groups[found_group]["L"]
                new_item["W"] = dimension_groups[found_group]["W"] 
                new_item["H"] = dimension_groups[found_group]["H"]
                normalized.append(new_item)
            else:
                group_key = (item["L"], item["W"], item["H"], item["NoID"], item["rotate"])
                dimension_groups[group_key] = item
                normalized.append(item)
                
        return normalized

    def sort_layers_by_z(self, container):
        """Sắp xếp layers theo Z tăng dần (Z1 ở dưới cùng, Zn ở trên cùng)"""
        layers = container["layers"]
        layers_sorted = sorted(layers, key=lambda x: x["z"])
        
        current_z = 0
        for idx, layer in enumerate(layers_sorted):
            layer["name"] = f"Lớp Z{idx+1}"
            layer["z"] = current_z
            for box in layer["boxes"]:
                box["z"] = current_z
            current_z += layer["height"]
        
        container["layers"] = layers_sorted

    def analyze_rotation_improvement(self, raw_items, cL, cW, cH):
        analysis = {
            "improved_items": [],
            "summary": {}
        }
        
        item_types = defaultdict(list)
        for item in raw_items:
            item_types[item["NoID"]].append(item)
        
        for item_type, items in item_types.items():
            if not items:
                continue
                
            sample_item = items[0]
            L, W, H = sample_item["L"], sample_item["W"], sample_item["H"]
            
            if sample_item["rotate"] != 1:
                continue
            
            orientations = [
                (L, W, H),
                (L, H, W),
                (W, L, H),
                (W, H, L),
                (H, L, W),
                (H, W, L)
            ]
            
            best_count = 0
            best_orientation = orientations[0]
            
            for orientation in orientations:
                count = self.calculate_possible_count(orientation[0], orientation[1], orientation[2], cL, cW, cH)
                if count > best_count:
                    best_count = count
                    best_orientation = orientation
            
            original_count = self.calculate_possible_count(L, W, H, cL, cW, cH)
            
            if best_count > original_count:
                improvement = ((best_count - original_count) / original_count) * 100
                
                analysis["improved_items"].append({
                    "type": item_type,
                    "original": (L, W, H),
                    "best_orientation": best_orientation,
                    "original_count": original_count,
                    "best_count": best_count,
                    "improvement": improvement,
                    "quantity": len(items)
                })
        
        analysis["improved_items"].sort(key=lambda x: x["improvement"], reverse=True)
        
        if analysis["improved_items"]:
            total_items = sum(item["quantity"] for item in analysis["improved_items"])
            avg_improvement = sum(item["improvement"] for item in analysis["improved_items"]) / len(analysis["improved_items"])
            analysis["summary"] = {
                "total_improved_types": len(analysis["improved_items"]),
                "total_improved_items": total_items,
                "avg_improvement": avg_improvement
            }
        
        return analysis

    def calculate_possible_count(self, L, W, H, cL, cW, cH):
        count_x = cL // L
        count_y = cW // W  
        count_z = cH // H
        
        total = count_x * count_y * count_z
        
        count_x2 = cL // L
        count_y2 = cW // H
        count_z2 = cH // W
        
        total2 = count_x2 * count_y2 * count_z2
        
        return max(total, total2)

    # =============================================================
    # DISPLAY FUNCTIONS
    # =============================================================
    
    def display_advanced_results(self):
        self.result_text.delete("1.0", "end")
        if not self.result: 
            self.result_text.insert("end", "Không có kết quả!\n", "WARN")
            return

        total_items = sum(c["packed_count"] for c in self.result)
        total_volume = sum(c["packed_vol"] for c in self.result)
        cont_volume = (self.container_length.get() * 
                      self.container_width.get() * 
                      self.container_height.get())
        overall_fill_rate = (total_volume / (cont_volume * len(self.result))) * 100
        
        best_strategy = self.result[0].get("best_strategy", "Không xác định")
        
        self.result_text.insert("end", "BÁO CÁO TỐI ƯU NÂNG CAO\n", "CONT")
        self.result_text.insert("end", "="*50 + "\n")
        self.result_text.insert("end", f"Chiến lược tốt nhất: {best_strategy}\n", "BEST")
        self.result_text.insert("end", f"Tổng số xe: {len(self.result)}\n")
        self.result_text.insert("end", f"Tổng kiện hàng: {total_items}\n")
        self.result_text.insert("end", f"Độ đầy trung bình: {overall_fill_rate:.1f}%\n")
        
        if self.allow_stacking_in_layer.get():
            stack_strategy = self.stack_strategy.get()
            strategy_name = "2D packing cục bộ" if stack_strategy == "2d_packing" else "tách riêng" if stack_strategy == "separate" else "cùng vị trí"
            self.result_text.insert("end", f"CẢI TIẾN: Kích hoạt chồng item thấp cùng layer (chiến lược: {strategy_name})\n", "BEST")
        
        if self.allow_height_tolerance.get():
            tolerance_value = self.height_tolerance_var.get()
            self.result_text.insert("end", f"CẢI TIẾN: Ưu tiên item chênh cao ≤ {tolerance_value}mm cùng layer\n", "BEST")
        
        self.result_text.insert("end", "="*50 + "\n\n")

        for c_idx, c in enumerate(self.result):
            vol_used = c['packed_vol']
            fill_rate = (vol_used/cont_volume)*100
            
            strategy_info = c.get("strategy", "Không xác định")
            time_info = f"{c.get('time', 0):.2f}s" if "time" in c else "N/A"
            
            self.result_text.insert("end", f"[{c['name']}] ", "CONT")
            self.result_text.insert("end", f"- {c['packed_count']} kiện - Đầy {fill_rate:.1f}%\n")
            self.result_text.insert("end", f"  Chiến lược: {strategy_info} - Thời gian: {time_info}\n")
            
            for l_idx, l in enumerate(c["layers"]):
                area_used = sum(b["L"]*b["W"] for b in l["boxes"])
                area_floor = self.container_length.get()*self.container_width.get()
                area_rate = (area_used/area_floor)*100
                
                self.result_text.insert("end", f"  └─ {l['name']} ", "LAYER")
                self.result_text.insert("end", f"(Z={l['z']}mm, Cao {l['height']}mm) - fill: {area_rate:.1f}% - {len(l['boxes'])} kiện\n")
                
                type_stats = {}
                rotated_stats = {"rotated": 0, "not_rotated": 0}
                stacked_stats = {"stacked": 0, "not_stacked": 0}
                stack_level_stats = {}
                
                for b in l["boxes"]:
                    key = f"{b['NoID']}: {b['L']}x{b['W']}x{b['H']}"
                    type_stats[key] = type_stats.get(key, 0) + 1
                    
                    if b.get("rotated", False):
                        rotated_stats["rotated"] += 1
                    else:
                        rotated_stats["not_rotated"] += 1
                    
                    if b.get("stacked", False):
                        stacked_stats["stacked"] += 1
                        stack_level = b.get("stack_level", 1)
                        stack_level_stats[stack_level] = stack_level_stats.get(stack_level, 0) + 1
                    else:
                        stacked_stats["not_stacked"] += 1
                
                for item_type, count in type_stats.items():
                    self.result_text.insert("end", f"      ▪ {item_type}: {count} kiện\n", "ITEM")
                
                if rotated_stats["rotated"] > 0:
                    self.result_text.insert("end", f"      ▪ Đã xoay: {rotated_stats['rotated']} kiện\n", "ITEM")
                    self.result_text.insert("end", f"      ▪ Không xoay: {rotated_stats['not_rotated']} kiện\n", "ITEM")
                
                if self.allow_stacking_in_layer.get() and stacked_stats["stacked"] > 0:
                    self.result_text.insert("end", f"      ▪ Đã chồng: {stacked_stats['stacked']} kiện\n", "BEST")
                    for level in sorted(stack_level_stats.keys()):
                        if level > 1:
                            self.result_text.insert("end", f"        ↳ Tầng {level}: {stack_level_stats[level]} kiện\n", "BEST")
            
            self.result_text.insert("end", "\n")

        self.result_text.insert("end", "THỐNG KÊ TỔNG QUAN\n", "CONT")
        self.result_text.insert("end", "="*50 + "\n")
        
        all_items = []
        for c in self.result:
            for l in c["layers"]:
                all_items.extend(l["boxes"])
        
        type_summary = Counter(item["NoID"] for item in all_items)
        for item_type, count in type_summary.most_common():
            self.result_text.insert("end", f"  {item_type}: {count} kiện\n", "ITEM")

        self.display_rotation_analysis()

    def display_rotation_analysis(self):
        if not self.rotation_analysis or not self.rotation_analysis["improved_items"]:
            return
            
        analysis = self.rotation_analysis
        summary = analysis["summary"]
        
        self.result_text.insert("end", "\nPHÂN TÍCH XOAY 90° TỐI ƯU\n", "ROTATE")
        self.result_text.insert("end", "="*50 + "\n", "ROTATE")
        self.result_text.insert("end", f"Có {summary['total_improved_types']} loại item sẽ tối ưu hơn nếu xoay\n", "ROTATE")
        self.result_text.insert("end", f"Tổng cộng {summary['total_improved_items']} kiện hàng có thể cải thiện\n", "ROTATE")
        self.result_text.insert("end", f"Cải thiện trung bình: {summary['avg_improvement']:.1f}%\n", "ROTATE")
        self.result_text.insert("end", "\n")
        
        self.result_text.insert("end", "CHI TIẾT CÁC ITEM NÊN XOAY:\n", "ROTATE")
        for i, item in enumerate(analysis["improved_items"][:10]):
            self.result_text.insert("end", f"{i+1}. {item['type']}:\n", "ROTATE")
            self.result_text.insert("end", f"   Kích thước gốc: {item['original'][0]}×{item['original'][1]}×{item['original'][2]}mm\n")
            self.result_text.insert("end", f"   Kích thước tối ưu: {item['best_orientation'][0]}×{item['best_orientation'][1]}×{item['best_orientation'][2]}mm\n")
            self.result_text.insert("end", f"   Số lượng xếp được: {item['original_count']} → {item['best_count']} (+{item['improvement']:.1f}%)\n")
            self.result_text.insert("end", f"   Số lượng hiện có: {item['quantity']} kiện\n")
            self.result_text.insert("end", "\n")
        
        if len(analysis["improved_items"]) > 10:
            self.result_text.insert("end", f"... và {len(analysis['improved_items']) - 10} loại item khác\n", "ROTATE")
        
        self.result_text.insert("end", "GỢI Ý: Hãy xoay thủ công các item này để tối ưu hơn!\n", "ROTATE")

    # =============================================================
    # VISUALIZATION FUNCTIONS - IMPROVED STACKING DISPLAY
    # =============================================================
    
    def draw_cross_sections(self):
        if not self.result:
            return
            
        for ax in self.ax_cross:
            ax.clear()
            
        container_idx = self.cb_container.current()
        if container_idx < 0:
            container_idx = 0
            
        if container_idx >= len(self.result):
            return
            
        container = self.result[container_idx]
        cL = self.container_length.get()
        cW = self.container_width.get()
        cH = self.container_height.get()
        
        cross_positions = [2000, 5000, 8000, 11000]
        colors = ['red', 'blue', 'green', 'orange']
        
        for i, x_pos in enumerate(cross_positions):
            if i >= len(self.ax_cross):
                break
                
            ax = self.ax_cross[i]
            ax.add_patch(Rectangle((0, 0), cW, cH, fill='lightgray', edgecolor='black', alpha=0.3))
            
            for layer in container["layers"]:
                for box in layer["boxes"]:
                    if box["x"] <= x_pos <= box["x"] + box["L"]:
                        y_pos = box["y"]
                        z_pos = box["z"]
                        width = box["W"]
                        height = box["H"]
                        
                        color_idx = hash(box["NoID"]) % len(colors)
                        color = colors[color_idx]
                        
                        edgecolor = 'red' if box.get("rotated", False) else 'black'
                        linewidth = 2 if box.get("rotated", False) else 0.8
                        
                        rect = Rectangle((y_pos, z_pos), width, height, 
                                       facecolor=color, edgecolor=edgecolor, 
                                       alpha=0.7, linewidth=linewidth)
                        ax.add_patch(rect)
                        
                        # Thêm visual cho item chồng
                        if box.get("stacked", False):
                            stack_level = box.get("stack_level", 1)
                            if stack_level == 2:
                                ax.add_patch(Rectangle((y_pos, z_pos), width, height, 
                                             fill=False, edgecolor='green', linewidth=3, linestyle='-'))
                            elif stack_level == 3:
                                ax.add_patch(Rectangle((y_pos, z_pos), width, height, 
                                             fill=False, edgecolor='orange', linewidth=3, linestyle='-'))
            
            self.add_z_labels_to_cross_section(ax, container, cW, cH)
    
            ax.set_xlim(-300, cW)
            ax.set_ylim(0, cH)
            ax.set_aspect('equal')
            ax.set_title(f'Mặt cắt tại {x_pos/1000:.1f}m', fontsize=10)
            ax.set_xlabel('Chiều rộng (mm)')
            ax.tick_params(axis='y', labelsize=8)
            ax.grid(True, alpha=0.3)
    
        self.fig_cross.tight_layout()
        self.cv_cross.draw()

    def add_z_labels_to_cross_section(self, ax, container, cW, cH):
        """Thêm nhãn Z1, Z2, Z3... bên trái trục Z"""
        for layer in container["layers"]:
            z_center = layer["z"] + layer["height"] / 2
            layer_name = layer["name"].replace("Lớp ", "").replace("Z", "Z")
            
            ax.text(-150, z_center, layer_name, 
                   ha='center', va='center', 
                   fontsize=6, fontweight='bold', color='darkblue',
                   bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow", alpha=0.9, edgecolor='darkblue'))
            
            ax.axhline(y=layer["z"], color='gray', linestyle='--', alpha=0.5, linewidth=0.8)
            ax.axhline(y=layer["z"] + layer["height"], color='gray', linestyle='--', alpha=0.5, linewidth=0.8)

    def draw_advanced_charts(self, container, layer_idx):
        self.ax_top.clear()
        L, W = self.container_length.get(), self.container_width.get()
        self.ax_top.add_patch(Rectangle((0, 0), L, W, fc="#F8F8FF", ec="navy", lw=2))
        
        cmap = plt.get_cmap("tab20")
        layers_to_show = container["layers"] if layer_idx == -1 else [container["layers"][layer_idx]] if 0 <= layer_idx < len(container["layers"]) else []

        for i, l in enumerate(container["layers"]):
            if layer_idx != -1 and i != layer_idx: 
                continue
            
            alpha = 1.0 if layer_idx == -1 else 0.7
            if layer_idx == -1:
                alpha = 1.0 - (i * 0.8 / len(container["layers"]))
            
            for j, b in enumerate(l["boxes"]):
                color = cmap((hash(b["NoID"]) % 20) / 20)
                
                edgecolor = 'red' if b.get("rotated", False) else 'black'
                linewidth = 2 if b.get("rotated", False) else 0.8
                
                rect = Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                               fc=color, ec=edgecolor, alpha=alpha, lw=linewidth)
                self.ax_top.add_patch(rect)
                
                # Thêm visual cho item chồng
                if b.get("stacked", False):
                    stack_level = b.get("stack_level", 1)
                    if stack_level == 2:
                        self.ax_top.add_patch(Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                                               fill=False, ec='green', lw=3, linestyle='-'))
                    elif stack_level == 3:
                        self.ax_top.add_patch(Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                                               fill=False, ec='orange', lw=3, linestyle='-'))
                    
                    if b["L"] * b["W"] > L * W * 0.02:
                        font_size = max(3, min(7, int(b["L"] * 0.012)))
                        self.ax_top.text(b["x"] + b["L"]/2, b["y"] + b["W"]/2, 
                                       f"T{stack_level}", ha='center', va='center', 
                                       fontsize=font_size, alpha=0.9, weight='bold', color='red')
            
                # Hiển thị thông tin
                if b["L"] * b["W"] > L * W * 0.02:
                    font_size = max(3, min(7, int(b["L"] * 0.012)))
                    text_color = 'red' if b.get("rotated", False) else 'black'
                    text_content = f"{b['NoID']}: {b['L']}x{b['W']}x{b['H']}"
                    self.ax_top.text(b["x"] + b["L"]/2, b["y"] + b["W"]/2, 
                                   text_content, ha='center', va='center', 
                                   fontsize=font_size, alpha=0.9, weight='bold', color=text_color)

        self.ax_top.set_xlim(0, L)
        self.ax_top.set_ylim(0, W)
        self.ax_top.set_aspect("equal")
        title = "Mặt bằng - Thuật toán G-F"
        if layer_idx != -1:
            title += f" - {container['layers'][layer_idx]['name']}"
        self.ax_top.set_title(title, fontsize=8)
        # self.ax_top.set_xlabel("Chiều dài container (mm)")
        # self.ax_top.set_ylabel("Chiều rộng container (mm)")
        self.cv_top.draw()

        self.ax_el.clear()
        H = self.container_height.get()
        self.ax_el.add_patch(Rectangle((0, 0), L, H, fc="#FFFAF0", ec="brown", lw=2))
        
        for i, l in enumerate(layers_to_show):
            for b in l["boxes"]:
                color = cmap((hash(b["NoID"]) % 20) / 20)
                edgecolor = 'red' if b.get("rotated", False) else 'black'
                linewidth = 2 if b.get("rotated", False) else 0.8
                
                rect = Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                               fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
                self.ax_el.add_patch(rect)
                
                if b.get("stacked", False):
                    stack_level = b.get("stack_level", 1)
                    if stack_level == 2:
                        self.ax_el.add_patch(Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                                             fill=False, ec='green', lw=3, linestyle='-'))
                    elif stack_level == 3:
                        self.ax_el.add_patch(Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                                             fill=False, ec='orange', lw=3, linestyle='-'))
                
                if b["L"] * b["H"] > L * H * 0.02:
                    font_size = max(3, min(7, int(b["L"] * 0.012)))
                    text_color = 'red' if b.get("rotated", False) else 'black'
                    self.ax_el.text(b["x"] + b["L"]/2, b["z"] + b["H"]/2, 
                                  b["NoID"], ha='center', va='center', 
                                  fontsize=font_size, alpha=0.9, weight='bold', color=text_color)
        
        self.ax_el.set_xlim(0, L)
        self.ax_el.set_ylim(0, H)
        self.ax_el.set_aspect("equal")
        self.ax_el.set_title("Mặt đứng - Xếp từ dưới lên", fontsize=10)
        self.ax_el.set_xlabel("Chiều dài container (mm)")
        self.cv_el.draw()

    def update_visualizer_controls(self):
        if not self.result:
            return
        self.cb_container['values'] = [c["name"] for c in self.result]
        self.cb_container.current(0)
        self.on_cont_change(None)

    def update_full_visualizer_controls(self):
        if not self.result:
            return
        self.full_cb_container['values'] = [c["name"] for c in self.result]
        self.full_cb_container.current(0)
        self.on_full_cont_change(None)

    def on_cont_change(self, event):
        idx = self.cb_container.current()
        if idx < 0:
            return
        cont = self.result[idx]
        lyrs = ["Tất cả"] + [l["name"] for l in cont["layers"]]
        self.cb_layer['values'] = lyrs
        self.cb_layer.current(0)
        self.draw_advanced_charts(cont, -1)
        self.draw_cross_sections()

    def on_layer_change(self, event):
        c_idx = self.cb_container.current()
        l_idx = self.cb_layer.current()
        if c_idx < 0:
            return
        cont = self.result[c_idx]
        self.draw_advanced_charts(cont, l_idx - 1)

    def on_full_cont_change(self, event):
        idx = self.full_cb_container.current()
        if idx < 0:
            return
        cont = self.result[idx]
        lyrs = ["Tất cả"] + [l["name"] for l in cont["layers"]]
        self.full_cb_layer['values'] = lyrs
        self.full_cb_layer.current(0)
        self.draw_full_size_chart()

    def on_full_layer_change(self, event):
        self.draw_full_size_chart()

    def on_full_view_change(self, event):
        self.draw_full_size_chart()

    def draw_full_size_chart(self):
        self.full_ax.clear()
        if not self.result: 
            self.full_ax.text(0.5, 0.5, "Không có dữ liệu để hiển thị", 
                            ha='center', va='center', transform=self.full_ax.transAxes, fontsize=14)
            self.full_canvas.draw()
            return

        c_idx = self.full_cb_container.current()
        if c_idx < 0:
            return
        
        container = self.result[c_idx]
        l_idx = self.full_cb_layer.current()
        view_type = self.full_cb_view.get()
        
        if l_idx == 0:
            layers_to_show = container["layers"]
        else:
            layers_to_show = [container["layers"][l_idx-1]] if l_idx-1 < len(container["layers"]) else []

        if view_type == "Mặt Bằng (Top)":
            self.draw_full_top_view(container, layers_to_show)
        else:
            self.draw_full_elevation_view(container, layers_to_show)
        
        self.full_canvas.draw()

    def draw_full_top_view(self, container, layers_to_show):
        L, W = self.container_length.get(), self.container_width.get()
        self.full_ax.add_patch(Rectangle((0, 0), L, W, fc="#F8F8FF", ec="navy", lw=3))
        
        cmap = plt.get_cmap("tab20")
        
        for i, l in enumerate(container["layers"]):
            if layers_to_show and l not in layers_to_show:
                continue
                
            alpha = 0.8
            for j, b in enumerate(l["boxes"]):
                color = cmap((hash(b["NoID"]) % 20) / 20)
                edgecolor = 'red' if b.get("rotated", False) else 'black'
                linewidth = 2 if b.get("rotated", False) else 1.2
                
                rect = Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                               fc=color, ec=edgecolor, alpha=alpha, lw=linewidth)
                self.full_ax.add_patch(rect)
                
                # Thêm visual cho item chồng
                if b.get("stacked", False):
                    stack_level = b.get("stack_level", 1)
                    if stack_level == 2:
                        self.full_ax.add_patch(Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                                               fill=False, ec='green', lw=3, linestyle='-'))
                    elif stack_level == 3:
                        self.full_ax.add_patch(Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                                               fill=False, ec='orange', lw=3, linestyle='-'))
                    
                    if b["L"] * b["W"] > L * W * 0.01:
                        font_size = max(8, min(14, int(b["L"] * 0.04)))
                        self.full_ax.text(b["x"] + b["L"]/2, b["y"] + b["W"]/2, 
                                        f"T{stack_level}", ha='center', va='center', 
                                        fontsize=font_size, alpha=0.9, weight='bold', color='red')
                
                # Hiển thị thông tin
                if b["L"] * b["W"] > L * W * 0.01:
                    font_size = max(8, min(14, int(b["L"] * 0.04)))
                    text_color = 'red' if b.get("rotated", False) else 'black'
                    text_content = f"{b['NoID']}: {b['L']}x{b['W']}x{b['H']}"
                    self.full_ax.text(b["x"] + b["L"]/2, b["y"] + b["W"]/2, 
                                   text_content, ha='center', va='center', 
                                   fontsize=font_size, alpha=0.9, weight='bold', color=text_color)

        self.full_ax.set_xlim(0, L)
        self.full_ax.set_ylim(0, W)
        self.full_ax.set_aspect("equal")
        
        title = f"MẶT BẰNG CONTAINER - {container['name']}"
        if layers_to_show and len(layers_to_show) == 1:
            title += f" - {layers_to_show[0]['name']}"
        self.full_ax.set_title(title, fontsize=16, weight='bold', pad=20)
        self.full_ax.set_xlabel("Chiều dài container (mm)", fontsize=6.25)
        self.full_ax.set_ylabel("Chiều rộng container (mm)", fontsize=6.25)
        
        self.full_ax.grid(True, alpha=0.3)
        
        total_boxes = sum(len(l["boxes"]) for l in (layers_to_show if layers_to_show else container["layers"]))
        stacked_count = sum(1 for l in (layers_to_show if layers_to_show else container["layers"]) 
                           for b in l["boxes"] if b.get("stacked", False))
        stack_strategy = self.stack_strategy.get()
        strategy_name = "2D packing cục bộ" if stack_strategy == "2d_packing" else "tách riêng" if stack_strategy == "separate" else "cùng vị trí"
        
        info_text = f"Tổng số kiện: {total_boxes} | Đã chồng: {stacked_count} | Chiến lược: {strategy_name}"
        if self.allow_height_tolerance.get():
            tolerance_value = self.height_tolerance_var.get()
            info_text += f" | Tolerance: ≤ {tolerance_value}mm"
        self.full_ax.text(0.02, 0.98, info_text, 
                         transform=self.full_ax.transAxes, fontsize=12, 
                         bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.8),
                         verticalalignment='top')

    def draw_full_elevation_view(self, container, layers_to_show):
        L, H = self.container_length.get(), self.container_height.get()
        self.full_ax.add_patch(Rectangle((0, 0), L, H, fc="#FFFAF0", ec="brown", lw=3))
        
        cmap = plt.get_cmap("tab20")
        
        for i, l in enumerate(layers_to_show):
            for b in l["boxes"]:
                color = cmap((hash(b["NoID"]) % 20) / 20)
                edgecolor = 'red' if b.get("rotated", False) else 'black'
                linewidth = 2 if b.get("rotated", False) else 1.2
                
                rect = Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                               fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
                self.full_ax.add_patch(rect)
                
                if b.get("stacked", False):
                    stack_level = b.get("stack_level", 1)
                    if stack_level == 2:
                        self.full_ax.add_patch(Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                                               fill=False, ec='green', lw=3, linestyle='-'))
                    elif stack_level == 3:
                        self.full_ax.add_patch(Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                                               fill=False, ec='orange', lw=3, linestyle='-'))
                
                if b["L"] * b["H"] > L * H * 0.01:
                    font_size = max(8, min(14, int(b["L"] * 0.04)))
                    text_color = 'red' if b.get("rotated", False) else 'black'
                    self.full_ax.text(b["x"] + b["L"]/2, b["z"] + b["H"]/2, 
                                  b["NoID"], ha='center', va='center', 
                                  fontsize=font_size, alpha=0.9, weight='bold', color=text_color)
        
        self.full_ax.set_xlim(0, L)
        self.full_ax.set_ylim(0, H)
        self.full_ax.set_aspect("equal")
        
        title = f"MẶT ĐỨNG CONTAINER - {container['name']}"
        if layers_to_show and len(layers_to_show) == 1:
            title += f" - {layers_to_show[0]['name']}"
        self.full_ax.set_title(title, fontsize=16, weight='bold', pad=20)
        self.full_ax.set_xlabel("Chiều dài container (mm)", fontsize=6.25)
        
        self.full_ax.grid(True, alpha=0.3)
        
        total_boxes = sum(len(l["boxes"]) for l in (layers_to_show if layers_to_show else container["layers"]))
        self.full_ax.text(0.02, 0.98, f"Tổng số kiện: {total_boxes}", 
                         transform=self.full_ax.transAxes, fontsize=12, 
                         bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.8),
                         verticalalignment='top')

    def export_full_pdf(self):
        if not self.result: 
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất!")
            return
            
        fp = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if fp: 
            try:
                self.full_fig.savefig(fp, dpi=300, bbox_inches='tight')
                messagebox.showinfo("Thành công", f"Đã lưu biểu đồ layer hiện tại dưới dạng PDF!\n{fp}")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể lưu file PDF:\n{str(e)}")

    def export_all_layers_pdf(self):
        if not self.result: 
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất!")
            return
        
        fp = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if not fp: 
            return
            
        try:
            with PdfPages(fp) as pdf:
                for c_idx, container in enumerate(self.result):
                    fig_all, ax_all = plt.subplots(figsize=(12, 8))
                    self._draw_container_top_view(ax_all, container, container["layers"])
                    ax_all.set_title(f"MẶT BẰNG - {container['name']} (Tất cả layers)", fontsize=16, weight='bold')
                    pdf.savefig(fig_all, bbox_inches='tight')
                    plt.close(fig_all)
                    
                    for l_idx, layer in enumerate(container["layers"]):
                        fig_layer, ax_layer = plt.subplots(figsize=(12, 8))
                        self._draw_container_top_view(ax_layer, container, [layer])
                        ax_layer.set_title(f"MẶT BẰNG - {container['name']} - {layer['name']}", fontsize=16, weight='bold')
                        pdf.savefig(fig_layer, bbox_inches='tight')
                        plt.close(fig_layer)
                    
                    fig_el_all, ax_el_all = plt.subplots(figsize=(12, 8))
                    self._draw_container_elevation_view(ax_el_all, container, container["layers"])
                    ax_el_all.set_title(f"MẶT ĐỨNG - {container['name']} (Tất cả layers)", fontsize=16, weight='bold')
                    pdf.savefig(fig_el_all, bbox_inches='tight')
                    plt.close(fig_el_all)
                    
                    for l_idx, layer in enumerate(container["layers"]):
                        fig_el_layer, ax_el_layer = plt.subplots(figsize=(12, 8))
                        self._draw_container_elevation_view(ax_el_layer, container, [layer])
                        ax_el_layer.set_title(f"MẶT ĐỨNG - {container['name']} - {layer['name']}", fontsize=16, weight='bold')
                        pdf.savefig(fig_el_layer, bbox_inches='tight')
                        plt.close(fig_el_layer)
                
            messagebox.showinfo("Thành công", f"Đã lưu tất cả layers dưới dạng PDF!\n{fp}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể lưu file PDF:\n{str(e)}")

    def _draw_container_top_view(self, ax, container, layers_to_show):
        L, W = self.container_length.get(), self.container_width.get()
        ax.add_patch(Rectangle((0, 0), L, W, fc="#F8F8FF", ec="navy", lw=2))
        
        cmap = plt.get_cmap("tab20")
        
        for l in layers_to_show:
            for b in l["boxes"]:
                color = cmap((hash(b["NoID"]) % 20) / 20)
                edgecolor = 'red' if b.get("rotated", False) else 'black'
                linewidth = 2 if b.get("rotated", False) else 1
                
                rect = Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                               fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
                ax.add_patch(rect)
                
                # Thêm visual cho item chồng
                if b.get("stacked", False):
                    stack_level = b.get("stack_level", 1)
                    if stack_level == 2:
                        ax.add_patch(Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                                     fill=False, ec='green', lw=2, linestyle='-'))
                    elif stack_level == 3:
                        ax.add_patch(Rectangle((b["x"], b["y"]), b["L"], b["W"], 
                                     fill=False, ec='orange', lw=2, linestyle='-'))
                
                # Hiển thị thông tin
                if b["L"] * b["W"] > L * W * 0.01:
                    font_size = max(8, min(12, int(b["L"] * 0.03)))
                    text_color = 'red' if b.get("rotated", False) else 'black'
                    text_content = f"{b['NoID']}: {b['L']}x{b['W']}x{b['H']}"
                    ax.text(b["x"] + b["L"]/2, b["y"] + b["W"]/2, 
                           text_content, ha='center', va='center', 
                           fontsize=font_size, alpha=0.9, weight='bold', color=text_color)

        ax.set_xlim(0, L)
        ax.set_ylim(0, W)
        ax.set_aspect("equal")
        ax.set_xlabel("Chiều dài container (mm)")
        ax.set_ylabel("Chiều rộng container (mm)")
        ax.grid(True, alpha=0.3)

    def _draw_container_elevation_view(self, ax, container, layers_to_show):
        L, H = self.container_length.get(), self.container_height.get()
        ax.add_patch(Rectangle((0, 0), L, H, fc="#FFFAF0", ec="brown", lw=2))
        
        cmap = plt.get_cmap("tab20")
        
        for l in layers_to_show:
            for b in l["boxes"]:
                color = cmap((hash(b["NoID"]) % 20) / 20)
                edgecolor = 'red' if b.get("rotated", False) else 'black'
                linewidth = 2 if b.get("rotated", False) else 1
                
                rect = Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                               fc=color, ec=edgecolor, alpha=0.8, lw=linewidth)
                ax.add_patch(rect)
                
                if b.get("stacked", False):
                    stack_level = b.get("stack_level", 1)
                    if stack_level == 2:
                        ax.add_patch(Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                                     fill=False, ec='green', lw=2, linestyle='-'))
                    elif stack_level == 3:
                        ax.add_patch(Rectangle((b["x"], b["z"]), b["L"], b["H"], 
                                     fill=False, ec='orange', lw=2, linestyle='-'))
                
                if b["L"] * b["H"] > L * H * 0.01:
                    font_size = max(8, min(12, int(b["L"] * 0.03)))
                    text_color = 'red' if b.get("rotated", False) else 'black'
                    ax.text(b["x"] + b["L"]/2, b["z"] + b["H"]/2, 
                           b["NoID"], ha='center', va='center', 
                           fontsize=font_size, alpha=0.9, weight='bold', color=text_color)
        
        ax.set_xlim(0, L)
        ax.set_ylim(0, H)
        ax.set_aspect("equal")
        ax.set_xlabel("Chiều dài container (mm)")
        ax.grid(True, alpha=0.3)

    def export_cross_sections_pdf(self):
        if not self.result: 
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất!")
            return
        
        fp = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        if not fp: 
            return
            
        try:
            with PdfPages(fp) as pdf:
                container_idx = self.cb_container.current()
                if container_idx < 0:
                    container_idx = 0
                    
                if container_idx >= len(self.result):
                    return
                    
                container = self.result[container_idx]
                cL = self.container_length.get()
                cW = self.container_width.get()
                cH = self.container_height.get()
                
                cross_positions = [2000, 5000, 8000, 11000]
                cross_titles = [
                    "Mặt cắt ngang tại vị trí 2.0m",
                    "Mặt cắt ngang tại vị trí 5.0m", 
                    "Mặt cắt ngang tại vị trí 8.0m",
                    "Mặt cắt ngang tại vị trí 11.0m"
                ]
                
                colors = ['red', 'blue', 'green', 'orange']
                
                for i, (x_pos, title) in enumerate(zip(cross_positions, cross_titles)):
                    fig_width = 6.2
                    fig_height = 8.77
                    fig, ax = plt.subplots(figsize=(fig_width, fig_height))
                    
                    ax.add_patch(Rectangle((0, 0), cW, cH, fill='lightgray', edgecolor='black', alpha=0.3, linewidth=2))
                    
                    boxes_at_section = []
                    
                    for layer in container["layers"]:
                        for box in layer["boxes"]:
                            if box["x"] <= x_pos <= box["x"] + box["L"]:
                                boxes_at_section.append(box)
                
                    for box in boxes_at_section:
                        y_pos = box["y"]
                        z_pos = box["z"]
                        width = box["W"]
                        height = box["H"]
                        
                        color_idx = hash(box["NoID"]) % len(colors)
                        color = colors[color_idx]
                        
                        edgecolor = 'red' if box.get("rotated", False) else 'black'
                        linewidth = 2 if box.get("rotated", False) else 1.5
                        
                        rect = Rectangle((y_pos, z_pos), width, height, 
                                       facecolor=color, edgecolor=edgecolor, alpha=0.8, linewidth=linewidth)
                        ax.add_patch(rect)
                        
                        # Thêm visual cho item chồng
                        if box.get("stacked", False):
                            stack_level = box.get("stack_level", 1)
                            if stack_level == 2:
                                ax.add_patch(Rectangle((y_pos, z_pos), width, height, 
                                             fill=False, edgecolor='green', linewidth=3, linestyle='-'))
                            elif stack_level == 3:
                                ax.add_patch(Rectangle((y_pos, z_pos), width, height, 
                                             fill=False, edgecolor='orange', linewidth=3, linestyle='-'))
                        
                        ax.text(y_pos + width/2, z_pos + height/2, 
                               box["NoID"], 
                               ha='center', va='center', 
                               fontsize=12, fontweight='bold', color='black')
                    
                    self.add_z_labels_to_cross_section(ax, container, cW, cH)
                    
                    ax.set_xlim(-300, cW)
                    ax.set_ylim(0, cH)
                    ax.set_aspect('equal')
                    
                    title_with_info = f'{title}\n{container["name"]} - Số kiện: {len(boxes_at_section)}'
                    ax.set_title(title_with_info, fontsize=16, weight='bold', pad=20)
                    ax.set_xlabel('Chiều rộng container (mm)', fontsize=14)
                    
                    ax.grid(True, alpha=0.5, linewidth=0.5)
                    
                    unique_items = list(set([box["NoID"] for box in boxes_at_section]))
                    if unique_items:
                        legend_text = "Các loại cấu kiện: " + ", ".join(unique_items)
                        fig.text(0.5, 0.01, legend_text, ha='center', fontsize=10, 
                                bbox=dict(boxstyle="round", facecolor="lightblue", alpha=0.8))
                    
                    fig.tight_layout(pad=1.0, rect=[0, 0.05, 1, 0.95])
                    pdf.savefig(fig, bbox_inches='tight', dpi=300)
                    plt.close(fig)
            
            messagebox.showinfo("Thành công", f"Đã xuất 4 mặt cắt ngang dưới dạng PDF!\n{fp}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể lưu file PDF:\n{str(e)}")

    # =============================================================
    # DXF EXPORT FUNCTIONS - IMPROVED VERSION
    # =============================================================
    
    def export_dxf(self):
        """Export all containers to DXF with 4 cross sections and top view with layers Z1, Z2,..."""
        if not self.result:
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất!")
            return
            
        if not DXF_AVAILABLE:
            messagebox.showerror("Lỗi", "Thư viện ezdxf không khả dụng! Vui lòng cài đặt: pip install ezdxf")
            return
        
        folder = filedialog.askdirectory(title="Chọn thư mục lưu file DXF")
        if not folder:
            return
            
        try:
            for container in self.result:
                self._export_container_dxf_with_layers(container, folder)
                
            messagebox.showinfo("Thành công", f"Đã xuất tất cả container dưới dạng DXF!\nThư mục: {folder}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể xuất file DXF:\n{str(e)}")

    def _export_container_dxf_with_layers(self, container, folder):
        """Export a container to DXF with 4 cross sections and top view with layers"""
        try:
            # Create DXF document
            doc = ezdxf.new('R2010')
            doc.header['$INSUNITS'] = 4  # Millimeters
            
            msp = doc.modelspace()
            
            cL = self.container_length.get()
            cW = self.container_width.get()
            cH = self.container_height.get()

            # DXF debug logging
            debug_enabled = getattr(self, 'dxf_debug_var', tk.BooleanVar(value=False)).get()
            debug_lines = []
            
            # Create layers
            doc.layers.add("CONTAINER", color=7)
            doc.layers.add("ITEMS", color=3)  # layer for block refs in cross-sections
            doc.layers.add("TEXT", color=1)
            doc.layers.add("DIMENSIONS", color=5)
            
            # Create layers for each container layer (Z1, Z2,...)
            for layer in container["layers"]:
                layer_name = layer['name'].replace(" ", "_")
                doc.layers.add(layer_name, color=3)
            
            # Create blocks for each item type
            block_definitions = {}
            for layer in container["layers"]:
                for box in layer["boxes"]:
                    no_id = box["NoID"]
                    is_rotated = box.get("rotated", False)
                    is_stacked = box.get("stacked", False)
                    stack_level = box.get("stack_level", 1)
                    
                    block_suffix = "_Ro" if is_rotated else ""
                    block_suffix += "_S" if is_stacked else ""
                    if is_stacked:
                        block_suffix += f"T{stack_level}"
                    
                    block_name = f"{no_id}{block_suffix}"
                    
                    if block_name not in block_definitions:
                        block = doc.blocks.new(name=block_name)
                        
                        block.add_lwpolyline([
                            (0, 0),
                            (box["W"], 0),
                            (box["W"], box["H"]),
                            (0, box["H"]),
                            (0, 0)
                        ])
                        
                        # Text content
                        text_content = f"{no_id}"
                        if is_rotated:
                            text_content += " (R)"
                        if is_stacked:
                            text_content += f" T{stack_level}"
                        
                        text = block.add_text(
                            text_content,
                            dxfattribs={
                                'height': 25.25,
                                'color': 1,
                            }
                        )
                        text.set_placement(
                            (box["W"]/2, box["H"]/2),
                            align=TextEntityAlignment.MIDDLE_CENTER
                        )
                        block_definitions[block_name] = True
            
            # Define 4 cross section positions
            section_positions = [2000, 5000, 8000, 11000]
            section_titles = ["Section 2.0m", "Section 5.0m", "Section 8.0m", "Section 11.0m"]
            section_x_offsets = [0, 3000, 6000, 9000]
            
            # Draw 4 cross sections
            for i, (x_pos, title, x_offset) in enumerate(zip(section_positions, section_titles, section_x_offsets)):
                # Draw container frame for cross section
                msp.add_lwpolyline([
                    (x_offset, 0),
                    (x_offset + cW, 0),
                    (x_offset + cW, cH),
                    (x_offset, cH),
                    (x_offset, 0)
                ], dxfattribs={'layer': 'CONTAINER'})
                
                # Find boxes in cross section
                boxes_at_section = []
                
                for layer in container["layers"]:
                    for box in layer["boxes"]:
                        if box["x"] <= x_pos <= box["x"] + box["L"]:
                            boxes_at_section.append(box)
                
                # Draw boxes in cross section using blocks
                for box in boxes_at_section:
                    no_id = box["NoID"]
                    is_rotated = box.get("rotated", False)
                    is_stacked = box.get("stacked", False)
                    stack_level = box.get("stack_level", 1)
                    
                    block_suffix = "_Ro" if is_rotated else ""
                    block_suffix += "_S" if is_stacked else ""
                    if is_stacked:
                        block_suffix += f"T{stack_level}"
                    
                    block_name = f"{no_id}{block_suffix}"

                    # Ensure block exists in document (defensive: avoid missing block refs)
                    created_block = False
                    try:
                        _ = doc.blocks.get(block_name)
                    except (KeyError, ezdxf.DXFKeyError):
                        created_block = True
                        # Create a simple block definition if missing (same geometry as originally intended)
                        blk = doc.blocks.new(name=block_name)
                        blk.add_lwpolyline([
                            (0, 0),
                            (box["W"], 0),
                            (box["W"], box["H"]),
                            (0, box["H"]),
                            (0, 0)
                        ])

                    insert_x = float(x_offset) + float(box["y"])
                    insert_y = float(box["z"])

                    # Insert blockref at (x offset + y, z)
                    msp.add_blockref(
                        block_name,
                        (insert_x, insert_y),
                        dxfattribs={
                            'layer': 'ITEMS',
                        }
                    )

                    if debug_enabled:
                        debug_lines.append(f"CrossSection '{title}' at x={x_pos} -> insert {block_name} at ({insert_x},{insert_y}) (created_block={created_block})")
                
                # Add cross section title
                title_text = msp.add_text(
                    f"{title} - {len(boxes_at_section)} kiện",
                    dxfattribs={
                        'layer': 'TEXT',
                        'height': 120,
                        'color': 1
                    }
                )
                title_text.set_placement(
                    (x_offset + cW/2, cH + 200),
                    align=TextEntityAlignment.MIDDLE_CENTER
                )
                
                # Add container dimensions
                msp.add_text(
                    f"{cW} x {cH} mm",
                    dxfattribs={
                        'layer': 'DIMENSIONS',
                        'height': 80,
                        'color': 5
                    }
                ).set_placement(
                    (x_offset + cW/2, -200),
                    align=TextEntityAlignment.MIDDLE_CENTER
                )
            
            # Add top views for each layer separated vertically to avoid overlap
            top_view_y_offset = -cH - 2000
            layer_spacing = 5000  # mm gap between consecutive top view layers
            
            # Draw each layer's top view in its own positioned frame (stacked downward)
            for layer_idx, layer in enumerate(container["layers"]):
                layer_name = layer['name'].replace(" ", "_")
                frame_y = top_view_y_offset - layer_idx * layer_spacing

                # Draw container frame for this layer's top view
                msp.add_lwpolyline([
                    (0, frame_y),
                    (cL, frame_y),
                    (cL, frame_y + cW),
                    (0, frame_y + cW),
                    (0, frame_y)
                ], dxfattribs={'layer': 'CONTAINER'})

                # Draw boxes for this layer using top-view blocks and apply per-layer vertical offset
                for box in layer["boxes"]:
                    no_id = box["NoID"]
                    is_rotated = box.get("rotated", False)
                    is_stacked = box.get("stacked", False)
                    stack_level = box.get("stack_level", 1)

                    top_block_name = f"{no_id}_Top_{box['L']}x{box['W']}x{box['H']}"
                    if top_block_name not in block_definitions:
                        block = doc.blocks.new(name=top_block_name)
                        # Draw rectangle in block (1:1 scale) for top view
                        block.add_lwpolyline([
                            (0, 0),
                            (box["L"], 0),
                            (box["L"], box["W"]),
                            (0, box["W"]),
                            (0, 0)
                        ])
                        # Text content for top view
                        text_content = f"{no_id}: {box['L']}x{box['W']}x{box['H']}"
                        if is_rotated:
                            text_content += "\n(R)"
                        if is_stacked:
                            text_content += f"\nT{stack_level}"
                        text = block.add_text(
                            text_content,
                            dxfattribs={
                                'height': 40.25,
                                'color': 1,
                            }
                        )
                        text.set_placement(
                            (box["L"]/2, box["W"]/2),
                            align=TextEntityAlignment.MIDDLE_CENTER
                        )
                        block_definitions[top_block_name] = True

                    # Insert top view block with per-layer offset so layers don't overlap
                    msp.add_blockref(
                        top_block_name,
                        (box["x"], frame_y + box["y"]),
                        dxfattribs={
                            'layer': layer_name,
                        }
                    )

                    if debug_enabled:
                        debug_lines.append(f"TopView Layer '{layer_name}' -> insert {top_block_name} at ({box['x']},{frame_y + box['y']})")

                # Add per-layer top view title and dimensions
                msp.add_text(
                    f"{layer['name']} - TOP VIEW - {len(layer['boxes'])} kiện",
                    dxfattribs={
                        'layer': 'TEXT',
                        'height': 120,
                        'color': 1
                    }
                ).set_placement(
                    (cL/2, frame_y + cW + 300),
                    align=TextEntityAlignment.MIDDLE_CENTER
                )

                msp.add_text(
                    f"{cL} x {cW} mm",
                    dxfattribs={
                        'layer': 'DIMENSIONS',
                        'height': 80,
                        'color': 5
                    }
                ).set_placement(
                    (cL/2, frame_y - 300),
                    align=TextEntityAlignment.MIDDLE_CENTER
                )
            
            # Add main title
            total_items = sum(len(layer["boxes"]) for layer in container["layers"])
            main_title = msp.add_text(
                f"CONTAINER: {container['name']} - Tổng: {total_items} kiện",
                dxfattribs={
                    'layer': 'TEXT',
                    'height': 150,
                    'color': 1
                }
            )
            main_title.set_placement(
                (10500, cH + 500),
                align=TextEntityAlignment.MIDDLE_CENTER
            )
            
            # Save file
            filename = f"{container['name']}_CrossSections_TopView.dxf".replace(" ", "_")
            filepath = os.path.join(folder, filename)
            doc.saveas(filepath)

            # Write debug log if enabled
            if debug_enabled:
                try:
                    debug_fp = os.path.join(folder, f"{container['name']}_DXF_DEBUG.txt")
                    with open(debug_fp, 'w', encoding='utf-8') as f:
                        f.write('\n'.join(debug_lines))
                except Exception as e:
                    # Non-fatal: just print to console
                    print(f"Failed to write DXF debug file: {e}")

        except Exception as e:
            raise Exception(f"Lỗi khi xuất DXF cho container {container['name']}: {str(e)}")

    def export_dxf_layers(self):
        """Export all layers top_view to a single *.dxf file for each container"""
        if not self.result:
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất!")
            return
            
        if not DXF_AVAILABLE:
            messagebox.showerror("Lỗi", "Thư viện ezdxf không khả dụng! Vui lòng cài đặt: pip install ezdxf")
            return
        
        folder = filedialog.askdirectory(title="Chọn thư mục lưu file DXF Layers")
        if not folder:
            return
            
        try:
            for container in self.result:
                self._export_container_layers_dxf(container, folder)
                
            messagebox.showinfo("Thành công", f"Đã xuất tất cả layers dưới dạng DXF!\nThư mục: {folder}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể xuất file DXF Layers:\n{str(e)}")

    def _export_container_layers_dxf(self, container, folder):
        """Export all layers of container to a single DXF file, each layer on a separate DXF layer"""
        try:
            doc = ezdxf.new('R2010')
            doc.header['$INSUNITS'] = 4
            
            msp = doc.modelspace()
            
            cL = self.container_length.get()
            cW = self.container_width.get()

            # DXF debug logging
            debug_enabled = getattr(self, 'dxf_debug_var', tk.BooleanVar(value=False)).get()
            debug_lines = []
            
            # Create layers
            doc.layers.add("CONTAINER", color=7)
            doc.layers.add("TEXT", color=1)
            
            # Create DXF layers for each container layer
            for layer in container["layers"]:
                layer_name = layer['name'].replace(" ", "_")
                doc.layers.add(layer_name, color=3)
            
            # Create blocks for items
            block_definitions = {}
            for layer in container["layers"]:
                for box in layer["boxes"]:
                    no_id = box["NoID"]
                    is_rotated = box.get("rotated", False)
                    is_stacked = box.get("stacked", False)
                    stack_level = box.get("stack_level", 1)
                    
                    block_suffix = "_Ro" if is_rotated else ""
                    block_suffix += "_S" if is_stacked else ""
                    if is_stacked:
                        block_suffix += f"T{stack_level}"
                    
                    block_name = f"{no_id}{block_suffix}"
                    
                    if block_name not in block_definitions:
                        block = doc.blocks.new(name=block_name)
                        block.add_lwpolyline([
                            (0, 0),
                            (box["L"], 0),
                            (box["L"], box["W"]),
                            (0, box["W"]),
                            (0, 0)
                        ])
                        # Text content
                        text_content = f"{no_id}: {box['L']}x{box['W']}x{box['H']}"
                        if is_rotated:
                            text_content += " (R)"
                        if is_stacked:
                            text_content += f" T{stack_level}"
                        text = block.add_text(
                            text_content,
                            dxfattribs={
                                'height': 25.25,
                                'color': 1,
                            }
                        )
                        text.set_placement(
                            (box["L"]/2, box["W"]/2),
                            align=TextEntityAlignment.MIDDLE_CENTER
                        )
                        block_definitions[block_name] = True
            
            layer_spacing = 5000  # mm gap between consecutive layer top views

            # Add container title (kept near the top-right of the sheet)
            title_text = msp.add_text(
                f"CONTAINER: {container['name']} - Total: {container['packed_count']} KIEN",
                dxfattribs={
                    'layer': 'TEXT',
                    'height': 200,
                    'color': 1
                }
            )
            title_text.set_placement(
                (cL/2, cW + 300 + 100),
                align=TextEntityAlignment.MIDDLE_CENTER
            )

            # Draw each layer on its own DXF frame (stacked downward with spacing)
            for layer_idx, layer in enumerate(container["layers"]):
                layer_name = layer['name'].replace(" ", "_")
                frame_y = - layer_idx * layer_spacing

                # Draw container frame for this specific layer's top view
                msp.add_lwpolyline([
                    (0, frame_y),
                    (cL, frame_y),
                    (cL, frame_y + cW),
                    (0, frame_y + cW),
                    (0, frame_y)
                ], dxfattribs={'layer': 'CONTAINER'})

                # Add layer title above the frame
                layer_title = msp.add_text(
                    f"{layer['name']} - {len(layer['boxes'])} kiện - Cao: {layer['height']}mm",
                    dxfattribs={
                        'layer': 'TEXT',
                        'height': 100,
                        'color': 1
                    }
                )
                layer_title.set_placement(
                    (cL/2, frame_y + cW + 100),
                    align=TextEntityAlignment.MIDDLE_CENTER
                )

                # Draw boxes in layer using blocks with per-layer vertical offset
                for box in layer["boxes"]:
                    no_id = box["NoID"]
                    is_rotated = box.get("rotated", False)
                    is_stacked = box.get("stacked", False)
                    stack_level = box.get("stack_level", 1)

                    block_suffix = "_Ro" if is_rotated else ""
                    block_suffix += "_S" if is_stacked else ""
                    if is_stacked:
                        block_suffix += f"T{stack_level}"

                    block_name = f"{no_id}{block_suffix}"

                    msp.add_blockref(
                        block_name,
                        (box["x"], frame_y + box["y"]),
                        dxfattribs={
                            'layer': layer_name,
                        }
                    )

                    if debug_enabled:
                        debug_lines.append(f"Layer '{layer_name}' -> insert {block_name} at ({box['x']},{frame_y + box['y']})")
            
            # Add legend
            legend_y = cW + 500
            for layer_idx, layer in enumerate(container["layers"]):
                layer_name = layer['name'].replace(" ", "_")
                legend_text = msp.add_text(
                    f"{layer['name']}: {len(layer['boxes'])} kiện, Cao: {layer['height']}mm",
                    dxfattribs={
                        'layer': 'TEXT',
                        'height': 80,
                        'color': layer_idx + 1
                    }
                )
                legend_text.set_placement(
                    (100, legend_y - layer_idx * 100),
                    align=TextEntityAlignment.LEFT
                )
            
            # Save file
            filename = f"{container['name']}_Layers.dxf".replace(" ", "_")
            filepath = os.path.join(folder, filename)
            doc.saveas(filepath)

            # Write debug log if enabled
            if debug_enabled:
                try:
                    debug_fp = os.path.join(folder, f"{container['name']}_DXF_LAYERS_DEBUG.txt")
                    with open(debug_fp, 'w', encoding='utf-8') as f:
                        f.write('\n'.join(debug_lines))
                except Exception as e:
                    print(f"Failed to write DXF Layers debug file: {e}")
            
        except Exception as e:
            raise Exception(f"Lỗi khi xuất DXF Layers cho container {container['name']}: {str(e)}")

    # =============================================================
    # UTILITY FUNCTIONS
    # =============================================================
    
    def load_sample(self):
        sample_data = [
            (2590, 300, 160, 54, "C100", 1),
            (2590, 300, 160, 10, "C101", 1),
            (2590, 300, 160, 1, "C102", 1),
            (2600, 172, 160, 5, "C106", 1),
            (2960, 230, 220, 27, "B109", 1),
            (2960, 230, 220, 1, "B156", 1),
            (2990, 330, 220, 78, "L100", 1),
            (2990, 330, 220, 9, "L101", 1),
            (2990, 330, 220, 4, "L152", 1),
            (2990, 395, 225, 24, "L106", 1),
            (2990, 395, 225, 3, "L107", 1),
            (2990, 395, 225, 1, "L153", 1),
            (3155, 230, 220, 3, "B100", 1),
            (3865, 212, 211, 5, "L180", 1),
            (3865, 230, 220, 10, "B164", 1),
            (3890, 330, 220, 50, "L156", 1),
            (3890, 398, 225, 5, "L157", 1),
            (4050, 230, 220, 15, "B103", 1),
            (4955, 230, 220, 9, "B106", 1),
            (4955, 230, 220, 5, "B161", 1),
            (4955, 230, 220, 1, "B162", 1),
            (6050, 230, 220, 5, "B180", 1),
        ]
        for d in sample_data: 
            self.data_tree.insert("", "end", values=d)

    def add_row_dialog(self):
        top = tk.Toplevel(self.root)
        top.title("Thêm hàng mới")
        top.geometry("350x250")
        top.transient(self.root)
        top.grab_set()
        
        ttk.Label(top, text="Thông tin hàng hóa:").pack(pady=2)
        
        frame = ttk.Frame(top)
        frame.pack(pady=10, padx=20, fill="both")
        
        vars = [tk.StringVar() for _ in range(6)]
        labels = ["Chiều dài (mm):", "Chiều rộng (mm):", "Chiều cao (mm):", "Số lượng:", "Mã hàng:", "Cho phép xoay (1/0):"]
        
        for i, label in enumerate(labels):
            ttk.Label(frame, text=label).grid(row=i, column=0, sticky="w", pady=2)
            if i == 5:
                rotate_cb = ttk.Combobox(frame, textvariable=vars[i], values=["1 - Có", "0 - Không"], state="readonly", width=13)
                rotate_cb.grid(row=i, column=1, sticky="ew", pady=2)
                rotate_cb.set("1 - Có")
            else:
                ttk.Entry(frame, textvariable=vars[i], width=15).grid(row=i, column=1, sticky="ew", pady=2)
        
        frame.columnconfigure(1, weight=1)
        
        def save():
            try:
                L, W, H, Q = int(vars[0].get()), int(vars[1].get()), int(vars[2].get()), int(vars[3].get())
                if L <= 0 or W <= 0 or H <= 0 or Q <= 0:
                    raise ValueError("Kích thước và số lượng phải > 0")
                    
                ID = vars[4].get() or f"Item{len(self.data_tree.get_children())+1}"
                
                rotate_str = vars[5].get()
                if "0" in rotate_str:
                    rotate = "0"
                else:
                    rotate = "1"
                    
                self.data_tree.insert("", "end", values=(L, W, H, Q, ID, rotate))
                top.destroy()
            except ValueError as e:
                messagebox.showerror("Lỗi", f"Dữ liệu không hợp lệ!\n{str(e)}")
        
        btn_frame = ttk.Frame(top)
        btn_frame.pack(pady=10)
        ttk.Button(btn_frame, text="Lưu", command=save).pack(side="left", padx=2)
        ttk.Button(btn_frame, text="Hủy", command=top.destroy).pack(side="left", padx=2)

    def import_excel(self):
        if not PANDAS_AVAILABLE: 
            messagebox.showerror("Lỗi", "Thư viện pandas không khả dụng!")
            return
            
        fp = filedialog.askopenfilename(
            filetypes=[("Excel files", "*.xlsx *.xls"), ("All files", "*.*")]
        )
        if fp:
            try:
                df = pd.read_excel(fp)
                for _, row in df.iterrows():
                    values = list(row)
                    while len(values) < 6:
                        values.append("1")
                    self.data_tree.insert("", "end", values=values[:6])
                    
                messagebox.showinfo("Thành công", f"Đã nhập {len(df)} dòng từ Excel!")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể đọc file Excel:\n{str(e)}")

    def delete_selected(self):
        selected = self.data_tree.selection()
        if not selected:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn dòng cần xóa!")
            return
            
        if messagebox.askyesno("Xác nhận", f"Xóa {len(selected)} dòng đã chọn?"):
            for s in selected: 
                self.data_tree.delete(s)

    def export_excel(self):
        if not self.result or not PANDAS_AVAILABLE: 
            messagebox.showwarning("Cảnh báo", "Không có dữ liệu để xuất hoặc thiếu thư viện pandas!")
            return
            
        fp = filedialog.asksaveasfilename(
            defaultextension=".xlsx",
            filetypes=[("Excel files", "*.xlsx"), ("All files", "*.*")]
        )
        if fp:
            try:
                data = []
                for c in self.result:
                    for l in c["layers"]:
                        for b in l["boxes"]:
                            data.append({
                                "Xe": c["name"], 
                                "Lớp": l["name"], 
                                "Mã hàng": b["NoID"], 
                                "Chiều dài": b["L"], 
                                "Chiều rộng": b["W"], 
                                "Chiều cao": b["H"],
                                "Vị trí X": b["x"], 
                                "Vị trí Y": b["y"], 
                                "Vị trí Z": b["z"],
                                "Đã xoay": "Có" if b.get("rotated", False) else "Không",
                                "Đã chồng": "Có" if b.get("stacked", False) else "Không",
                                "Tầng chồng": b.get("stack_level", 1),
                                "Thể tích": b["L"] * b["W"] * b["H"]
                            })
                
                df = pd.DataFrame(data)
                df.to_excel(fp, index=False)
                messagebox.showinfo("Thành công", f"Đã xuất {len(df)} dòng ra file Excel!")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể xuất file:\n{str(e)}")


# =============================================================
# LICENSE CHECK FUNCTION - SILENT VERSION
# =============================================================

def check_license():
    """Kiểm tra license: bắt buộc phải lấy được ngày từ web mới cho chạy."""
    try:
        import urllib.request
        import json
        from datetime import datetime

        # Các server thời gian dạng API JSON (ưu tiên)
        time_servers = [
            "http://worldtimeapi.org/api/timezone/Etc/UTC",
            "http://worldtimeapi.org/api/ip",
            "http://worldclockapi.com/api/json/utc/now",
            "https://timeapi.io/api/Time/current/zone?timeZone=UTC"
        ]

        # Các báo Việt Nam dùng để lấy thời gian từ HTTP header "Date"
        vn_sites = [
            "https://vnexpress.net",
            "https://dantri.com.vn",
            "https://tuoitre.vn",
            "https://zingnews.vn"
        ]

        fetched_time = None

        # 1) Thử lấy thời gian từ các API JSON
        for server in time_servers:
            try:
                req = urllib.request.Request(
                    server,
                    headers={'User-Agent': 'ContainerPackingApp/2.6'}
                )
                with urllib.request.urlopen(req, timeout=8) as response:
                    data = response.read().decode('utf-8')
                    json_data = json.loads(data)

                    time_str = None
                    if 'utc_datetime' in json_data:
                        time_str = json_data['utc_datetime']
                    elif 'datetime' in json_data:
                        time_str = json_data['datetime']
                    elif 'currentDateTime' in json_data:
                        time_str = json_data['currentDateTime']
                    elif 'dateTime' in json_data:
                        time_str = json_data['dateTime']

                    if time_str:
                        time_str_clean = time_str.split('+')[0].split('.')[0]

                        for fmt in [
                            "%Y-%m-%dT%H:%M:%S",
                            "%Y-%m-%d %H:%M:%S",
                            "%Y/%m/%d %H:%M:%S"
                        ]:
                            try:
                                fetched_time = datetime.strptime(time_str_clean, fmt)
                                break
                            except ValueError:
                                continue

                        if fetched_time:
                            break  # Chỉ cần 1 web OK là dừng

            except Exception:
                continue

        # 2) Nếu API quốc tế chết → dùng header Date của báo Việt Nam
        if not fetched_time:
            for site in vn_sites:
                try:
                    req = urllib.request.Request(
                        site,
                        method="HEAD",
                        headers={'User-Agent': 'Mozilla/5.0'}
                    )
                    with urllib.request.urlopen(req, timeout=8) as response:
                        date_str = response.headers.get("Date")
                        if date_str:
                            # Ví dụ: 'Tue, 05 Dec 2025 11:03:22 GMT'
                            for fmt in [
                                "%a, %d %b %Y %H:%M:%S %Z",
                                "%a, %d %b %Y %H:%M:%S"
                            ]:
                                try:
                                    fetched_time = datetime.strptime(date_str, fmt)
                                    break
                                except ValueError:
                                    continue
                        if fetched_time:
                            break
                except Exception:
                    continue

        # 3) Nếu KHÔNG lấy được thời gian từ bất kỳ web nào → KHÔNG CHO CHẠY
        if not fetched_time:
            return False

        # 4) Kiểm tra hạn sử dụng (80 ngày kể từ 01/12/2025)
        license_start_date = datetime(2025, 12, 1)
        days_used = (fetched_time - license_start_date).days

        if days_used > 80:
            return False

        return True

    except Exception:
        # Bất kỳ lỗi nào trong quá trình kiểm tra license → KHÔNG CHO CHẠY
        return False

# =============================================================
# PASSWORD AUTHENTICATION - SILENT LICENSE CHECK
# =============================================================

def ask_password(main_window):
    """Password authentication window - return True if OK, False if cancel/close/wrong"""
    pw_root = tk.Toplevel(main_window)
    pw_root.title("Access Verification")
    pw_root.geometry("350x180")
    pw_root.resizable(False, False)

    try:
        # Try to load icon if exists
        ICON_PATH = os.path.join(os.path.dirname(__file__), "ngoc_diep_icon_large.ico")
        if os.path.exists(ICON_PATH):
            pw_root.iconbitmap(ICON_PATH)
    except:
        pass

    pw_root.attributes("-topmost", True)

    # Tiêu đề
    title_label = tk.Label(
        pw_root,
        text="CONTAINER PACKING ADVANCED",
        font=("Segoe UI", 12, "bold"),
        fg="#0F7B3A"
    )
    title_label.pack(pady=2)

    tk.Label(
        pw_root,
        text="Enter your password:",
        font=("Segoe UI", 10)
    ).pack(pady=2)

    pw_var = tk.StringVar()
    entry = tk.Entry(
        pw_root,
        textvariable=pw_var,
        show="•",
        font=("Segoe UI", 11),
        width=20
    )
    entry.pack(pady=2)
    entry.focus()

    # Biến lưu kết quả xác thực
    auth_result = {"ok": False}

    def confirm():
        """Check password: ROUNDUP(((year*12 / month) + 971) * 12, 0)"""

        now = datetime.now()
        month = now.month
        year = now.year

        # Tính theo công thức Excel ROUNDUP
        calc_value = ((year * 12 / month) + 971) * 12
        real_pass = str(math.ceil(calc_value))

        if pw_var.get().strip() == real_pass:
            auth_result["ok"] = True
            pw_root.destroy()
        else:
            messagebox.showerror(
                "System error",
                "System error!\nContact the service"
            )
            auth_result["ok"] = False
            pw_var.set("")
            entry.focus_set()

    def cancel():
        """User bấm Hủy"""
        auth_result["ok"] = False
        pw_root.destroy()

    def on_closing():
        """User bấm nút X"""
        auth_result["ok"] = False
        pw_root.destroy()

    # Gắn xử lý nút X
    pw_root.protocol("WM_DELETE_WINDOW", on_closing)

    # Khung nút
    btn_frame = tk.Frame(pw_root)
    btn_frame.pack(pady=10)

    tk.Button(
        btn_frame,
        text="XÁC NHẬN",
        width=12,
        command=confirm,
        bg="#4CAF50",
        fg="white",
        font=("Segoe UI", 9, "bold")
    ).grid(row=0, column=0, padx=2)

    tk.Button(
        btn_frame,
        text="HỦY",
        width=12,
        command=cancel,
        bg="#f44336",
        fg="white",
        font=("Segoe UI", 9, "bold")
    ).grid(row=0, column=1, padx=2)

    # Enter = xác nhận
    pw_root.bind("<Return>", lambda event: confirm())

    # Không cho thao tác ngoài cửa sổ này
    pw_root.grab_set()
    pw_root.wait_window()

    # Trả về kết quả cho hàm gọi
    return auth_result["ok"]

# =============================================================
# MAIN APPLICATION LAUNCH - SILENT VERSION
# =============================================================
if __name__ == "__main__":
    # 1. SILENT license check - No console output
    if not check_license():
        # License check failed - exit silently without any message
        import sys
        sys.exit(0)

    # 2. Tạo main window (ẩn lúc đầu)
    root = tk.Tk()
    root.withdraw()

    # 3. Hiện cửa sổ nhập mật khẩu
    authenticated = ask_password(root)

    # 4. Nếu không xác thực được → thoát chương trình
    if not authenticated:
        root.destroy()
        import sys
        sys.exit(0)

    # 5. Đúng mật khẩu → hiện main window
    root.deiconify()

    try:
        # Try to load icon if exists
        ICON_PATH = os.path.join(os.path.dirname(__file__), "ngoc_diep_icon_large.ico")
        if os.path.exists(ICON_PATH):
            root.iconbitmap(ICON_PATH)
    except Exception:
        pass

    # 6. Start main application
    app = ContainerAppAdvanced(root)
    root.bind("<Escape>", app.clear_drag_selection)

    # Set window title
    root.title("CONTAINER PACKING ADVANCED - VERSION 3.0")

    # 7. Main event loop
    root.mainloop()                       