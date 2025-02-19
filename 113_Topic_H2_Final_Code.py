"""
Author: Cheng-Chun-Hsu, Yi-An-Chen
Date: 2025/02/19

The hole details of how to use this code is in Notion URL
Please check it before you use this code
"""
import tkinter as tk
import time
import sv_ttk
from tkinter import ttk, filedialog, messagebox, BooleanVar
from PIL import Image, ImageTk, ImageDraw
import os
import cv2
import numpy as np
import math
from ultralytics import YOLO
from ultralytics.utils.plotting import Annotator, colors
from shapely.geometry import Polygon
from shapely.geometry.point import Point
import mysql.connector
import datetime
import logging
import requests
import re
from collections import deque
from threading import Lock
from tkcalendar import DateEntry
import speech_recognition as sr

from scipy.spatial.distance import euclidean
from shapely.affinity import scale

# Root level of Tkinter building, don't change
root = tk.Tk()
root.title('Smart Security Management And Control Platform  Based on AI Image Recognition Technology')
root.iconphoto(False, tk.PhotoImage(file='fcu_iecs_logo.png'))
style = ttk.Style()
style.configure("Treeview", font=('Verdana', 16), rowheight=40)
style_heading = ttk.Style()
style_heading.configure("Treeview.Heading", font=('Verdana', 20))
image_cache = {}
y2_positions = deque(maxlen=10)
prev_y2_sum = None
r = sr.Recognizer()
# Models
# Make sure you have been trained the own model and put it in the same directory
# Every model have their corresponding names
model_person = YOLO('yolov8n.pt')
model_person_pose = YOLO('yolov8m-pose.pt')
model_gate = YOLO('gate_1107.pt')
model_cone = YOLO('cone.pt')
model_Weapon = YOLO('knife_1110.pt')
model_Violence = YOLO('0918Violence.pt')
model_Abnormal = YOLO('yolov8m.pt')
video_queue = []
current_video = None
Violence_queue = []
Weapon_queue = []
Falling_queue = []
AbnormalEvents_queue = []
ElectronicFence_queue = []
RollingDoor_queue = []
check_queues = {
    "Violence": Violence_queue,
    "Weapon": Weapon_queue,
    "Falling": Falling_queue,
    "AbnormalEvents": AbnormalEvents_queue,
    "ElectronicFence": ElectronicFence_queue,
    "RollingDoor": RollingDoor_queue
}
start_index = -1
video_total_frames = 0
cap = None
frame_queue1 = deque()  # 使用 deque 取代 list
frame_queue2 = deque()
queue_lock = Lock()
batch_size = 500
frame_limit = 0
fps = 0
Abnormal_count = []
abnormal_frame_count = 0
avg_person_count = 0
# Scale bar
scale_values = {
    "Violence": 0.1,
    "Weapon": 0.1,
    "RollingDoor": 0.1,
    "AbnormalEvents": 0.1,
    "ElectronicFence": 0.1,
    "Falling": 0.1
}

# Video Global

to_be_upload_type = []
# Global variables of rolling Door
names_gate = model_gate.model.names
names_person = model_person.model.names

# Global variables of ElectronicFence
counting_regions = [
    {
        "polygon": Polygon([]),  # Polygon points
    },
]

# 設定視窗的背景顏色和大小
root.configure(bg="black")
root.geometry("400x300")
root.state('zoomed')
current_frame = 0
keep_frame = 0
stay_frame = 0
waiting_second = 3
stay_second = 1
flag = [0, 0, 0]
flags = {
    'Violence': 0,
    'Weapon': 0,
    'Falling': 0,
    'ElectronicFence': 0,
    'RollingDoor': 0,
    'AbnormalEvents': 0
}

current_show_index = 0
recording = False
out = None
fourcc = cv2.VideoWriter_fourcc(*"mp4v")
out_path = None
if_log = False
frame_count = 0
last_add_time = None
if_upload = False
video_url = None
image_url = None
full_path = None
height = None
# Variable of Line user id, change it to your own,
user_id = 'INPUT YOUR LINE USER ID'

# We use 'MySQL Workbench', change this to your alvin cloud database(See README.md)
# 以下每一個都要換成你自己的不然雲端會動不了
connection = mysql.connector.connect(
    host="HOST",
    user="USER",  # 使用你的 MySQL 使用者名
    password="MYSQL PW",  # 使用你的 MySQL 密碼
    database="ui",  # 剛才創建的資料庫名稱
    port=6666,  # 切記要記得換Port, 不要打預設的3306
)
cursor = connection.cursor()

def get_latest_ID():
    cursor.execute("SELECT MAX(id) FROM events_2")
    record = cursor.fetchone()
    if record[0] is not None:
        return record[0]
    else:
        return 0
def get_all_records():
    cursor.execute("SELECT * FROM events_2")
    records = cursor.fetchall()

    return records
def extract_info(text):
    # Match patterns for date, date range, and time range
    date_pattern = r"(\d{1,2})月(\d{1,2})號"
    date_range_pattern = r"(\d{1,2})月(\d{1,2})號到(\d{1,2})月(\d{1,2})號"
    time_range_pattern = r"(上午|下午|晚上)?(\d{1,2})點(到|至)(上午|下午|晚上)?(\d{1,2})點"

    # Keywords to detect
    keywords = ["暴力", "危險物", "鐵捲門", "異常事件", "圍籬", "跌倒", "開啟", "關閉"]

    # Initialize empty variables for date, date range, and time range
    result = ""

    # Find date range matches (e.g., "幾月幾號到幾月幾號")
    date_range_match = re.search(date_range_pattern, text)
    if date_range_match:
        start_month = int(date_range_match.group(1))
        start_day = int(date_range_match.group(2))
        end_month = int(date_range_match.group(3))
        end_day = int(date_range_match.group(4))
        start_date = f"{start_month}月{start_day}號"
        end_date = f"{end_month}月{end_day}號"
        result += f"辨識到日期範圍: {start_date} 到 {end_date}\n"

    # Find single date match (e.g., "幾月幾號")
    if not date_range_match:  # Only look for single date if no date range is found
        date_match = re.search(date_pattern, text)
        if date_match:
            month = int(date_match.group(1))
            day = int(date_match.group(2))
            date_info = f"{month}月{day}號"
            result += f"辨識到日期: {date_info}\n"

    # Find time range matches (e.g., "幾點到幾點")
    time_range_match = re.search(time_range_pattern, text)
    if time_range_match:
        start_period = time_range_match.group(1) if time_range_match.group(1) else ""
        start_hour = int(time_range_match.group(2))
        end_period = time_range_match.group(4) if time_range_match.group(4) else ""
        end_hour = int(time_range_match.group(5))

        # Combine period and hour for start and end times
        start_time = f"{start_period}{start_hour}點"
        end_time = f"{end_period}{end_hour}點"

        result += f"辨識到時間範圍: {start_time} 到 {end_time}\n"

    # Detect specific keywords
    detected_keywords = [keyword for keyword in keywords if keyword in text]
    if detected_keywords:
        result += f"偵測到以下關鍵字: {', '.join(detected_keywords)}\n"
        change_mode_By_Sound(detected_keywords)

    # Output results based on what is found
    if not result:
        result = "未辨識到日期或時間資訊\n"

    return result
def start_recognition():
    with sr.Microphone() as source:
        text_area.insert(tk.END, "請說出您的需求...\n")
        audio = r.listen(source)
        try:
            text_area.insert(tk.END, "正在處理語音...\n")
            # Using Google Speech Recognition API
            text = r.recognize_google(audio, language='zh-TW')
            text_area.insert(tk.END, f"辨識結果: {text}\n")
            # Extract and display information
            result = extract_info(text)
            text_area.insert(tk.END, result)
        except sr.UnknownValueError:
            text_area.insert(tk.END, "Google Speech Recognition 無法辨識音訊\n")
        except sr.RequestError as e:
            text_area.insert(tk.END, f"無法從 Google Speech Recognition 服務請求結果; {e}\n")
def create_sound_recog_window():
    global sound_recog_window, text_area, r
    sound_recog_window = tk.Toplevel(root)
    sound_recog_window.title("語音辨識")
    sound_recog_window.geometry("500x400")

    # Create text area for displaying results
    text_area = tk.Text(sound_recog_window, wrap=tk.WORD)
    text_area.pack(expand=1, fill="both")

    # Create button to start speech recognition
    start_button = tk.Button(sound_recog_window, text="開始語音辨識", command=start_recognition)
    start_button.pack()
# 歷史列表點擊播放影片
def eventlist_play(video_url):
    global cap
    cap = cv2.VideoCapture(video_url)

    def update_frame():
        ret, frame = cap.read()
        if ret:
            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            img = Image.fromarray(frame)
            imgtk = ImageTk.PhotoImage(image=img)
            lbl.imgtk = imgtk
            lbl.config(image=imgtk)
            lbl.after(29, update_frame)
        else:
            cap.release()

    video_window = tk.Toplevel()
    video_window.title("Video Playback")

    lbl = tk.Label(video_window)
    lbl.pack()

    update_frame()


def show_all_event():
    global tree
    # 获取所有记录
    records = get_all_records()

    # 创建新窗口
    new_window = tk.Toplevel()
    new_window.title("All Records")
    new_window.state("zoomed")

    record_frame1 = tk.Frame(new_window)
    record_frame1.pack(fill='x')
    # 创建一个新的内部 Frame 用于水平居中
    center_frame = tk.Frame(record_frame1)
    center_frame.pack(side='top', padx=10, pady=10)
    record_frame2 = tk.Frame(new_window)
    record_frame2.pack(fill='both', expand=True)

    # 加入起始日期選擇
    start_label = tk.Label(center_frame, text="Start Date:", font=('Verdana', 12))
    start_label.pack(side='left', padx=5, pady=5)

    start_date = DateEntry(center_frame, width=12, background='darkblue', foreground='white', borderwidth=2)
    start_date.pack(side='left', padx=5, pady=5)

    # 加入結束日期選擇
    end_label = tk.Label(center_frame, text="End Date:", font=('Verdana', 12))
    end_label.pack(side='left', padx=5, pady=5)

    end_date = DateEntry(center_frame, width=12, background='darkblue', foreground='white', borderwidth=2)
    end_date.pack(side='left', padx=5, pady=5)

    # 小時選擇器的選項
    hours = [f"{i:02d}" for i in range(24)]  # 生成00到23的時間

    # 加入起始小時選擇
    start_hour_label = tk.Label(center_frame, text="Start Hour:", font=('Verdana', 12))
    start_hour_label.pack(side='left', padx=5, pady=5)

    start_hour_combo = ttk.Combobox(center_frame, values=hours, width=5)
    start_hour_combo.set(hours[0])  # 預設選擇00
    start_hour_combo.pack(side='left', padx=5, pady=5)

    # 加入結束小時選擇
    end_hour_label = tk.Label(center_frame, text="End Hour:", font=('Verdana', 12))
    end_hour_label.pack(side='left', padx=5, pady=5)

    end_hour_combo = ttk.Combobox(center_frame, values=hours, width=5)
    end_hour_combo.set(hours[23])  # 預設選擇23
    end_hour_combo.pack(side='left', padx=5, pady=5)

    # 將所有的Checkbutton水平排列
    vio_var = tk.IntVar()
    vio_check = tk.Checkbutton(center_frame, text="Violence", variable=vio_var, font=('Verdana', 12))
    vio_check.pack(side='left', padx=5, pady=5)

    weapon_var = tk.IntVar()
    weapon_check = tk.Checkbutton(center_frame, text="Weapon", variable=weapon_var, font=('Verdana', 12))
    weapon_check.pack(side='left', padx=5, pady=5)

    door_var = tk.IntVar()
    door_check = tk.Checkbutton(center_frame, text="RollingDoor", variable=door_var, font=('Verdana', 12))
    door_check.pack(side='left', padx=5, pady=5)

    abnormal_var = tk.IntVar()
    abnormal_check = tk.Checkbutton(center_frame, text="AbnormalEvents", variable=abnormal_var, font=('Verdana', 12))
    abnormal_check.pack(side='left', padx=5, pady=5)

    fence_var = tk.IntVar()
    fence_check = tk.Checkbutton(center_frame, text="ElectronicFence", variable=fence_var, font=('Verdana', 12))
    fence_check.pack(side='left', padx=5, pady=5)

    Falling_var = tk.IntVar()
    Falling_check = tk.Checkbutton(center_frame, text="Falling", variable=Falling_var, font=('Verdana', 12))
    Falling_check.pack(side='left', padx=5, pady=5)

    # 加入篩選按鈕
    search_button = tk.Button(center_frame, text="Search", command=lambda: filter_records(), font=('Verdana', 12))
    search_button.pack(side='left', padx=10, pady=5)
    record_scrollbar = tk.Scrollbar(record_frame2, orient="vertical")
    record_scrollbar.pack(side='right', fill='y')
    tree = ttk.Treeview(record_frame2, show='headings', yscrollcommand=record_scrollbar.set)
    tree.pack(fill='both', expand=True)
    record_scrollbar.config(command=tree.yview)
    tree['columns'] = ('id', 'type', 'time', 'video_url', 'risk_level', 'image_url')
    tree.heading('id', text='id', command=lambda: sort_treeview(tree, records, 0))
    tree.heading('type', text='type', command=lambda: sort_treeview(tree, records, 1))
    tree.heading('time', text='time', command=lambda: sort_treeview(tree, records, 2))
    tree.heading('video_url', text='video_url', command=lambda: sort_treeview(tree, records, 3))
    tree.heading('risk_level', text='risk_level', command=lambda: sort_treeview(tree, records, 4))
    tree.heading('image_url', text='image_url', command=lambda: sort_treeview(tree, records, 5))
    def update_treeview(data):
        # Clear current treeview
        for row in tree.get_children():
            tree.delete(row)
        # Insert filtered data
        for record in data:
            tree.insert('', 'end', values=record)
    def sort_treeview(treeview, data, col):
        data.sort(key=lambda x: x[col])
        update_treeview(data)
    def filter_records():
        start_date_str = start_date.get_date().strftime("%Y-%m-%d")
        end_date_str = end_date.get_date().strftime("%Y-%m-%d")
        start_hour_str = start_hour_combo.get()
        end_hour_str = end_hour_combo.get()

        event_types = {
            'Violence': vio_var.get(),
            'Weapon': weapon_var.get(),
            'RollingDoor': door_var.get(),
            'AbnormalEvents': abnormal_var.get(),
            'ElectronicFence': fence_var.get(),
            'Falling': Falling_var.get(),
        }

        filtered_records = filter_by_time_range_and_category(
            records, start_date_str, end_date_str, start_hour_str, end_hour_str, event_types
        )
        update_treeview(filtered_records)
    def on_item_click(event):
        if tree.selection():
            selected_item = tree.selection()[0]
            video_url = tree.item(selected_item, 'values')[3]
            eventlist_play(video_url)

    def filter_by_time_range_and_category(records, start_date_str, end_date_str, start_hour_str, end_hour_str,
                                          event_types):
        start_hour = int(start_hour_str)
        end_hour = int(end_hour_str)
        filtered_records = []
        for record in records:
            record_datetime = datetime.datetime.strptime(record[2], "%Y-%m-%d %H:%M:%S")

            if start_date_str <= record_datetime.strftime("%Y-%m-%d") <= end_date_str:
                record_hour = record_datetime.hour
                if start_hour <= record_hour <= end_hour:
                    if event_types.get(record[1], False):
                        filtered_records.append(record)
        return filtered_records
    update_treeview(records)
    tree.bind('<3>', choose_actions)
    def clear_filters():
        current_time = time.strftime('%m/%d/%y')
        start_date.set_date(current_time)
        end_date.set_date(current_time)
        start_hour_combo.set('00')
        end_hour_combo.set('23')
        vio_check.deselect()
        weapon_check.deselect()
        door_check.deselect()
        abnormal_check.deselect()
        fence_check.deselect()
        Falling_check.deselect()

        original_record = get_all_records()
        update_treeview(original_record)

    clear_button = tk.Button(center_frame, text="Reset", command=clear_filters, font=('Verdana', 12))
    clear_button.pack(side=tk.LEFT)
def update_risk_level(record_id, new_risk_level):
    # 確保 record_id 是整數
    record_id = int(record_id)
    cursor.execute("UPDATE events_2 SET risk_level = %s WHERE id = %s", (new_risk_level, record_id))
    connection.commit()

def adjust_risk_level():
    global tree
    selected_item = tree.focus()  # 獲取選中的項目
    if not selected_item:
        return
    # 從 Treeview 中取得選取項目的資料
    item_values = tree.item(selected_item, "values")
    record_id = item_values[0]  # 取得紀錄的 ID

    # 創建一個新視窗來選擇 risk_level
    def apply_risk_level():
        new_risk_level = risk_level_combo.get()

        update_risk_level(record_id, new_risk_level)
        #  messagebox.showinfo("更新成功", "Risk Level 已成功更新！")

        # 在 UI 中同步更新
        tree.item(selected_item, values=(record_id, *item_values[1:4], new_risk_level, item_values[5]))

        dialog.destroy()  # 關閉視窗

    # 彈出選擇視窗
    dialog = tk.Toplevel(root)
    dialog.title("Choose Risk Level")
    dialog.geometry("200x150")

    # Label 與下拉選單
    tk.Label(dialog, text="Choose Risk Level:").pack(pady=10)
    risk_level_combo = ttk.Combobox(dialog, values=["Undefined", "Low", "Medium", "High", "Critical"])
    risk_level_combo.set(item_values[4])  # 預設當前的 risk level
    risk_level_combo.pack(pady=5)

    # 按鈕
    tk.Button(dialog, text="Save", command=apply_risk_level).pack(pady=10)
def choose_actions(event):
    selected_item = tree.selection()  # 獲取選中項
    if not selected_item:
        return
    def on_item_click():
        if tree.selection():
            selected_item = tree.selection()[0]
            video_url = tree.item(selected_item, 'values')[3]
            eventlist_play(video_url)
    def intersection():
        action = actions_combo.get()  # 獲取選中項
        if action == 'adjust_risk_level':
            adjust_risk_level()
        elif action == 'check_video':
            on_item_click()

    actions = tk.Toplevel(root)
    actions.geometry("200x150")

    tk.Label(actions, text='Choose actions:', font=('Verdana', 12)).pack(pady=10)
    actions_combo = ttk.Combobox(actions, values=['adjust_risk_level', 'check_video'])
    actions_combo.pack(pady=5)

    tk.Button(actions, text='Confirm', command=intersection, font=('Verdana', 12)).pack(pady=10)
def update_time():
    current_time = time.strftime('%Y-%m-%d %H:%M:%S')
    time_label.config(text=f"Time: {current_time}")
    root.after(1000, update_time)


def create_rounded_rectangle(width, height, radius, fill_color):
    image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    draw.rounded_rectangle([(0, 0), (width, height)], radius, fill=fill_color)
    return image

def get_rounded_rectangle_image(width, height, radius, fill_color):
    key = (width, height, radius, fill_color)
    if key not in image_cache:
        image_cache[key] = create_rounded_rectangle(width, height, radius, fill_color)
    return image_cache[key]

def create_rounded_frame(parent, width, height, radius, fill_color, bg_color):
    rounded_rect_image = create_rounded_rectangle(width, height, radius, fill_color)
    rounded_rect_photo = ImageTk.PhotoImage(rounded_rect_image)
    label = tk.Label(parent, image=rounded_rect_photo, bd=0, bg=bg_color)  # 手动设置背景颜色
    label.image = rounded_rect_photo  # 保存引用
    frame = tk.Frame(label, bg=fill_color)
    frame.place(x=13, y=1, width=width-2*radius, height=height)
    return label, frame
def update_v_value(value):
    formatted_value = f"{float(value):.1f}"
    v_scale_value.config(text=f"Conf                {formatted_value}")
    scale_values["Violence"] = round(float(value), 1)
def update_w_value(value):
    formatted_value = f"{float(value):.1f}"
    w_scale_value.config(text=f"Conf                {formatted_value}")
    scale_values["Weapon"] = round(float(value), 1)

def update_d_value(value):
    formatted_value = f"{float(value):.1f}"
    d_scale_value.config(text=f"Conf                {formatted_value}")
    scale_values["RollingDoor"] = round(float(value), 1)

def update_g_value(value):
    formatted_value = f"{float(value):.1f}"
    g_scale_value.config(text=f"Conf                {formatted_value}")
    scale_values["AbnormalEvents"] = round(float(value), 1)

def update_e_value(value):
    formatted_value = f"{float(value):.1f}"
    e_scale_value.config(text=f"Conf                {formatted_value}")
    scale_values["ElectronicFence"] = round(float(value), 1)

def update_f_value(value):
    formatted_value = f"{float(value):.1f}"
    f_scale_value.config(text=f"Conf                {formatted_value}")
    scale_values["Falling"] = round(float(value), 1)
def add_history(id, event):
    global ElectronicFence_flag, recording, to_be_upload_type, dt_file_time
    global flags, file_time
    print(f'event: {event}')
    if not recording:
        dt_file_time = datetime.datetime.strptime(file_time, '%Y%m%d_%H%M%S')
        current_time = dt_file_time.strftime('%Y-%m-%d %H:%M:%S')
        if event:
            event_types_str = ', '.join(event)
            history.insert('', 'end', values=(id, event_types_str, current_time))


# 自定義標題欄框架


def classify(event):
    global current_event_index, classify_top, classify_top_event_label, classify_top_time_label, label, classify_top_width, classify_top_height, selected_item, btn1, btn2, btn3, btn4
    global full_path, save_path, img_Frame, img_label, img
    selected_item = history.selection()[0]
    history.selection_remove(selected_item)
    item_value = history.item(selected_item, 'values')
    event_name = item_value[0]

    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()

    classify_top_width = int(screen_width * 0.75)
    classify_top_height = int(screen_height * 0.75)

    x = (screen_width - classify_top_width) // 2
    y = (screen_height - classify_top_height) // 2

    classify_top = tk.Toplevel(root)
    classify_top.geometry(f"{classify_top_width}x{classify_top_height}+{x}+{y}")

    classify_top_event_label = tk.Label(classify_top, text=f'Event: {item_value[0]}', font=('Verdana', 20), pady=10)
    classify_top_event_label.pack(pady=10)
    classify_top_time_label = tk.Label(classify_top, text=f'Time: {item_value[2]}', font=('Verdana', 20), pady=10)
    classify_top_time_label.pack(pady=10)

    img_Frame = tk.Frame(classify_top)
    img_Frame.pack()

    previous_button = tk.Button(img_Frame, text='Previous', font=('Verdana', 20, 'bold'), command=previous_event)
    previous_button.pack(side=tk.LEFT, padx=50)
    next_button = tk.Button(img_Frame, text='Next', font=('Verdana', 20, 'bold'), command=next_event)
    next_button.pack(side=tk.RIGHT, padx=50)

    img_label = tk.Label(img_Frame, bg='lightgray')
    img_label.pack()

    image_path = save_path + '/' + f'{time_format(item_value[2])}.jpg'
    print(image_path)

    if image_path:
        image = Image.open(image_path)
        resized_image = image.resize((int(classify_top_width * 0.6), int(classify_top_height * 0.6)))
        img = ImageTk.PhotoImage(resized_image)
        img_label.config(image=img)
        img_label.image = img

    button_Frame = tk.Frame(classify_top, pady=20)
    button_Frame.pack(pady=20)
    btn1 = tk.Button(button_Frame, text='Low', activeforeground='green',
                     command=lambda item=selected_item: set_event_color(selected_item, 'green'), font=('Verdana', 20, 'bold'))
    btn1.pack(side=tk.LEFT, padx=50)

    btn2 = tk.Button(button_Frame, text='Medium', activeforeground='yellow',
                     command=lambda item=selected_item: set_event_color(selected_item, 'yellow'), font=('Verdana', 20, 'bold'))
    btn2.pack(side=tk.LEFT, padx=50)

    btn3 = tk.Button(button_Frame, text='High', activeforeground='orange',
                     command=lambda item=selected_item: set_event_color(selected_item, 'orange'), font=('Verdana', 20, 'bold'))
    btn3.pack(side=tk.LEFT, padx=50)

    btn4 = tk.Button(button_Frame, text='Critical', activeforeground='red',
                     command=lambda item=selected_item: set_event_color(selected_item, 'red'), font=('Verdana', 20, 'bold'))
    btn4.pack(side=tk.LEFT, padx=50)

    # 初始化 current_event_index
    current_event_index = history.get_children().index(selected_item)

def set_event_color(item, color):
    history.tag_configure(color, background=color)
    history.item(item, tags=(color,))

    def update_risk_level(item, color):
        new_risk_level = 'undefined'
        if color == 'green':
            new_risk_level = 'Low'
        elif color == 'yellow':
            new_risk_level = 'Medium'
        elif color == 'orange':
            new_risk_level = 'High'
        elif color == 'red':
            new_risk_level = 'Critical'

        record_id = int(history.item(item, 'values')[0])
        cursor.execute("UPDATE events_2 SET risk_level = %s WHERE id = %s", (new_risk_level, record_id))
        connection.commit()

    update_risk_level(item, color)

def previous_event():
    global current_event_index
    if current_event_index > 0:
        current_event_index -= 1
        update_event_info(current_event_index)


def next_event():
    global current_event_index
    if current_event_index < len(history.get_children()) - 1:
        current_event_index += 1
        update_event_info(current_event_index)
def update_event_info(event_index):
    global selected_item
    selected_item = history.get_children()[event_index]
    item_value = history.item(selected_item, 'values')
    event_name = item_value[0]

    classify_top_event_label.config(text=f'Event: {item_value[0]}')
    classify_top_time_label.config(text=f'Time: {item_value[2]}')
    image_path = save_path + '/' + f'{time_format(item_value[2])}.jpg'
    print(image_path)

    if image_path:
        image = Image.open(image_path)
        resized_image = image.resize((int(classify_top_width * 0.6), int(classify_top_height * 0.6)))  # 调整图片大小
        img = ImageTk.PhotoImage(resized_image)
        img_label.config(image=img)
        img_label.image = img

def display_frame(frame):
    global Frame_right, Frame6, canvas
    # 將幀從 BGR 轉換為 RGB
    frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
    frame = Image.fromarray(frame)
    # 更新 Frame_right 和 Frame6 的尺寸
    Frame_right.update_idletasks()
    Frame_right_width = Frame_right.winfo_width()
    Frame6_height = Frame6.winfo_height()
    Frame_right_height = Frame_right.winfo_height() - Frame6_height
    # 調整幀大小以適配 Frame_right
    frame_ratio = frame.width / frame.height
    Frame_right_ratio = Frame_right_width / Frame_right_height
    if frame_ratio > Frame_right_ratio:
        new_height = int(Frame_right_width / frame_ratio)
        frame = frame.resize((Frame_right_width, new_height), Image.LANCZOS)
    else:
        new_width = int(Frame_right_height * frame_ratio)
        frame = frame.resize((new_width, Frame_right_height), Image.LANCZOS)

    # 創建黑色背景來填充額外空間
    background = Image.new('RGB', (Frame_right_width, Frame_right_height), (0, 0, 0))
    background.paste(frame, ((Frame_right_width - frame.width) // 2, (Frame_right_height - frame.height) // 2))
    # 使用 ImageTk 轉換為 tkinter 可用的格式
    frame = ImageTk.PhotoImage(background)
    canvas.create_image(0, 0, anchor=tk.NW, image=frame)
    canvas.image = frame
    canvas.config(width=Frame_right_width, height=Frame_right_height)

# All subfunctions of detect function
def get_polar_angle(coordinate, center):
    dx = coordinate[0] - center[0]
    dy = coordinate[1] - center[1]
    return math.atan2(dy, dx)

def save_frame_as_image(frame):
    global full_path, recording
    global flags, file_time
    if not recording:
        file_time = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
        filename = f"{file_time}.jpg"
        full_path = os.path.join(save_path, filename)
        cv2.imwrite(full_path, frame)
def upload_video_to_imgur(video_path, max_attempts=3):
    global video_url, uploading_window, upload_bar, upload_val, a
    a += 12.5
    upload_bar['value'] = a
    upload_val.set(f'{int(a)}%')
    upload_bar.update()
    print(f"正在上傳影片: {video_path}")  # 调试输出
    client_id = 'YOU OWN ID'
    headers = {'Authorization': f'Client-ID {client_id}'}
    files = {'video': open(video_path, 'rb')}
    url = 'YOU OWN API'
    attempts = 0
    try:
        response = requests.post(url, headers=headers, files=files)
        response.raise_for_status()
        a += 12.5
        upload_bar['value'] = a
        upload_val.set(f'{int(a)}%')
        upload_bar.update()
        data = response.json()
        a += 12.5
        upload_bar['value'] = a
        upload_val.set(f'{int(a)}%')
        upload_bar.update()
        if 'data' in data and 'link' in data['data']:
            video_url = data['data']['link']
            a += 12.5
            upload_bar['value'] = a
            upload_val.set(f'{int(a)}%')
            upload_bar.update()
            print(f"更新的影片URL: {video_url}")
            return
        else:
            logging.error(f"Error uploading video: {data}")
            return
    except Exception as e:
        logging.error(f"Error uploading video: {str(e)}")
        attempts += 1
    logging.error("Failed to upload video after multiple attempts.")

def upload_image_to_imgur(max_attempts=3):
    global full_path, image_url, uploading_window, upload_bar, upload_val, a
    print(f"正在上傳圖片: {full_path}")
    client_id = 'YOU OWN CLIENT ID'
    headers = {'Authorization': f'Client-ID {client_id}'}
    files = {'image': open(full_path, 'rb')}
    # API of imgur
    url = 'YOU OWN API'
    attempts = 0

    try:
        response = requests.post(url, headers=headers, files=files)
        a += 12.5
        upload_bar['value'] = a
        upload_val.set(f'{int(a)}%')
        upload_bar.update()
        response.raise_for_status()
        a += 12.5
        upload_bar['value'] = a
        upload_val.set(f'{int(a)}%')
        upload_bar.update()
        data = response.json()
        a += 12.5
        upload_bar['value'] = a
        upload_val.set(f'{int(a)}%')
        upload_bar.update()
        if 'data' in data and 'link' in data['data']:
            image_url = data['data']['link']
            a += 12.5
            upload_bar['value'] = a
            upload_val.set(f'{int(a)}%')
            upload_bar.update()
            print(f"更新的圖片URL: {image_url}")
            return
        else:
            logging.error(f"Error uploading image: {data}")
            return
    except Exception as e:
        logging.error(f"Error uploading image: {str(e)}")
        attempts += 1
    logging.error("Failed to upload image after multiple attempts.")

def send_video_and_image(video_url, image_path):
    with open(image_path, 'rb') as image_file:
        data = {
            "video_url": video_url,
            "events_id": get_latest_ID() + 1
        }
        files = {
            "image": image_file
        }
        response = requests.post('https://flask-appfcudata-836365687310.asia-east2.run.app/receive_video_and_image', data=data, files=files)
        if response.status_code == 200:
            print("LineServer接收成功")
        else:
            print("LineServer接收失敗")
def reset_flag(flag_name):
    globals()[flag_name] = 0

def log_event(type='text', risk_level=None):
    global full_path, video_url, image_url
    print(f'log!!!!!!!')
    current_time = time.strftime('%Y-%m-%d %H:%M:%S')
    insert_query = "INSERT INTO events_2 (type, time, video_url, risk_level, image_url) VALUES (%s, %s, %s, %s, %s)"
    cursor.execute(insert_query, (type, current_time, video_url, risk_level, image_url))
    connection.commit()
    video_url = None
    image_url = None

def detect_event(event_type, frame, after_frame):
    if event_type == 'Violence':
        return Violence_Detection(frame, after_frame, scale_values['Violence'])
    if event_type == 'Weapon':
        selected_weapon = get_selected_weapons()
        return Weapon_Detection(frame, after_frame, scale_values['Weapon'], selected_weapon)
    if event_type == 'AbnormalEvents':
        return Abnormal_Detection(frame, after_frame, scale_values['AbnormalEvents'])
    if event_type == 'Falling':
        return Falling_Detection(frame, after_frame, scale_values['Falling'])
    if event_type == 'ElectronicFence':
        return ElectronicFence_Detection(frame, after_frame, scale_values['ElectronicFence'])
    if event_type == 'RollingDoor':
        return RolliongDoor_Detection(frame, after_frame, scale_values['RollingDoor'])
    else:
        return frame
def handle_events(event_name, after_frame):
    global flags, recording, out, fps, out_path, save_path, to_be_upload_type
    event = flags.get(event_name)
    print(f'event:{event}, event_name:{event_name}')
    if event and flags[event_name] == 1:
        save_frame_as_image(after_frame)
        add_history(get_latest_ID()+1, to_be_upload_type)
        if not recording:
            start_recording_if_needed(after_frame, event_name)

def reset_state():
    global current_frame, frame_queue1, frame_queue2
    current_frame = 0
    frame_queue1.clear()
    frame_queue2.clear()
    for event_type in flags:
        flags[event_type] = 0

def choose_import_video():
    global video_path, video_playing, video_queue
    path = None
    if not save_path_label.cget("text"):
        error_window = tk.Toplevel(root)

        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()

        error_window_width = int(screen_width * 0.24)
        error_window_height = int(screen_height * 0.1)

        x = (screen_width - error_window_width) // 2
        y = (screen_height - error_window_height) // 2

        error_window.geometry(f"{error_window_width}x{error_window_height}+{x}+{y}")
        error_message = tk.Label(error_window, text='Please choose a save location first!', font=('Verdana', 14))
        error_message.pack(anchor='center', fill='both', expand=True)
    elif Weapon_var.get() and not knife_var.get() and not bat_var.get():
        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()

        weapon_warning_width = 400
        weapon_warning_height = 150

        x = (screen_width - weapon_warning_width) // 2
        y = (screen_height - weapon_warning_height) // 2

        weapon_warning = tk.Toplevel(root)
        weapon_warning.geometry(f"{weapon_warning_width}x{weapon_warning_height}+{x}+{y}")
        tk.Label(weapon_warning, text="You haven't selected a weapon yet,\nare you sure you want to proceed?", font=('verdana', 14)).pack(anchor='center', fill='both', expand=True)
    else:
        path = filedialog.askdirectory()
    if path:
        video_files = [f for f in os.listdir(path) if f.lower().endswith(('.mp4', '.avi', '.mkv'))]
        if video_files:
            video_queue = [os.path.join(path, video) for video in video_files]
            play_next_video()

def play_next_video():
    global video_queue, current_video, video_playing
    if video_queue:
        current_video = video_queue.pop(0)  # 從清單中取出第一部影片
        now_playing_label.config(text=os.path.basename(current_video), font=('Verdana', 12, 'bold'))
        import_path_label.config(text=os.path.dirname(current_video), font=('Verdana', 12, 'bold'))
        play_video(current_video)  # 播放影片
def play_video(video_path):
    global video, current_frame, ElectronicFence_flag, video_playing, cap, fps, height, width, video_queue
    print(f'video_queue: {video_queue}')
    if video_path:
        print(f'video_path: {video_path}')
        video = cv2.VideoCapture(video_path)
        cap = video
        width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
        height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
        video.set(cv2.CAP_PROP_POS_FRAMES, current_frame)
        fps = cap.get(cv2.CAP_PROP_FPS)
        preload_frame()
    else:
        messagebox.showerror("Error", "Choose a valid video")

def preload_frame():
    global video, frame_queue1, after_frame, pressed, recording, frame_limit, current_frame, processed_frame, frame_queue2, fps, video_url, image_url, total_frames, cap
    print('preload!!!!')
    video_total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))  # 使用 video 而非 cap
    fps = cap.get(cv2.CAP_PROP_FPS)
    total_frames = int(5*fps)
    print(f'total_frame: {total_frames}')
    # 設置進度條窗口
    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()
    print('test')
    width = 350
    height = 100

    x = (screen_width - width) // 2
    y = (screen_height - height) // 2
    bar_window = tk.Toplevel(root)
    bar_window.geometry(f"{width}x{height}+{x}+{y}")
    tk.Label(bar_window, text='Loading...', font=('verdana', 12)).pack(pady=10)
    bar = ttk.Progressbar(bar_window, orient="horizontal", mode='determinate', length=300)
    bar.pack(pady=10)
    bar['maximum'] = video_total_frames
    val = tk.StringVar()
    val.set('0%')
    label = tk.Label(bar_window, textvariable=val, font=('Verdana', 12))
    label.pack()

    # 逐幀讀取與處理
    for _ in range(video_total_frames):
        ret, frame = cap.read()
        if not ret:
            break
        pressed = on_button_toggle()
        after_frame = frame

        # 根據 pressed 中的事件進行偵測處理
        for event_type in flags:
            if event_type in pressed:
                after_frame = detect_event(event_type, frame, after_frame)
        frame_queue2.append(after_frame)  # 將處理後的 frame 加入 queue

        # 更新進度條
        bar['value'] = len(frame_queue2)
        val.set(f'{int(len(frame_queue2) / video_total_frames * 100)}%')
        root.update()  # 立即更新視窗

    # 處理完畢後顯示 frame
    bar_window.destroy()  # 關閉進度條窗口
    show_frame()  # 顯示所有處理後的 frames

def choose_save_location():
    global save_path
    save_path = filedialog.askdirectory()
    if save_path:
        save_path_label.config(text=save_path)

# 以下皆為所有偵測相關的 Code
def preprocess_frame(frame):
    denoised_frame = cv2.GaussianBlur(frame, (5, 5), 0)

    lab = cv2.cvtColor(denoised_frame, cv2.COLOR_BGR2LAB)
    l, a, b = cv2.split(lab)
    clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
    cl = clahe.apply(l)
    limg = cv2.merge((cl, a, b))
    final_frame = cv2.cvtColor(limg, cv2.COLOR_LAB2BGR)

    return final_frame
def get_polar_angle(coordinate, center):
    dx = coordinate[0] - center[0]
    dy = coordinate[1] - center[1]
    return math.atan2(dy, dx)

def detect_gate(frame, after_frame, cof):
    global height, width
    results = model_gate.predict(source=frame, conf=0.6, classes=[0], verbose= False)
    boxes = results[0].boxes.xyxy.cpu()
    if len(boxes) > 0:
        annotator = Annotator(after_frame, line_width=2, example=str("Shutter"))
        for box in boxes:
            annotator.box_label(box, "Gate", color=colors(0, True))
            gate_coords = [(int(box[0]), height), (int(box[2]), height), (int(box[2]), 0), (int(box[0]), 0)]
            return Polygon(gate_coords), box, after_frame
    return None, None, after_frame
def detect_person(frame, after_frame, cof):
    results = model_person.predict(source=frame, classes=[0], verbose= False, conf=0.8)
    boxes = results[0].boxes.xyxy.cpu()
    if len(boxes) > 0:
        annotator = Annotator(after_frame, line_width=2, example=str("Person"))
        for box in boxes:
            annotator.box_label(box, "Person", color=colors(1, True))
            person_center = ((box[0] + box[2]) / 2, (box[1] + box[3]) / 2)
            return person_center, after_frame
    return None, after_frame
def Falling_Check1(left_vector1, left_vector2, right_vector1, right_vector2):
    cosine_angle = np.dot(left_vector1, left_vector2) / (np.linalg.norm(left_vector1) * np.linalg.norm(left_vector2))
    angle = np.arccos(cosine_angle)

    left_angle_degrees = np.degrees(angle)
    cosine_angle = np.dot(right_vector1, right_vector2) / (
                np.linalg.norm(right_vector1) * np.linalg.norm(right_vector2))
    angle = np.arccos(cosine_angle)
    right_angle_degrees = np.degrees(angle)

    if right_angle_degrees <= 90 and left_angle_degrees <= 90:
        return 1
    else:
        return 0

def Falling_Check2(head_point, s_point):
    x_s, y_s = s_point
    x_h, y_h = head_point
    fin = abs(y_s - y_h) / abs(x_s - x_h)
    ang = math.atan(fin)
    angle = np.degrees(abs(ang))
    if angle <= 50:
        return 1
    else:
        return 0
def Falling_Check3(height, width):
    if width / height > 1:
        return 1
    else:
        return 0
def hsv2bgr(h, s, v):
    h_i = int(h * 6)
    f = h * 6 - h_i
    p = v * (1 - s)
    q = v * (1 - f * s)
    t = v * (1 - (1 - f) * s)

    r, g, b = 0, 0, 0

    if h_i == 0:
        r, g, b = v, t, p
    elif h_i == 1:
        r, g, b = q, v, p
    elif h_i == 2:
        r, g, b = p, v, t
    elif h_i == 3:
        r, g, b = p, q, v
    elif h_i == 4:
        r, g, b = t, p, v
    elif h_i == 5:
        r, g, b = v, p, q

    return int(b * 255), int(g * 255), int(r * 255)

def Falling_random_color(id):
    h_plane = (((id << 2) ^ 0x937151) % 100) / 100.0
    s_plane = (((id << 3) ^ 0x315793) % 100) / 100.0
    return hsv2bgr(h_plane, s_plane, 1)

def detect_people(frame):
    results = model_Abnormal(frame)
    count = 0
    centers = []
    boxes = []
    for result in results:
        for box in result.boxes:
            if box.cls.item() == 0:
                count += 1
                center_x = (box.xyxy[0][0] + box.xyxy[0][2]) / 2
                center_y = (box.xyxy[0][1] + box.xyxy[0][3]) / 2
                centers.append((center_x.item(), center_y.item()))
                boxes.append(box)
    return results, count, centers, boxes
def distance_cal(centers, person_count, cof):
    count = 0
    threshold = 250
    len_centers = len(centers)
    for i in range(len_centers):
        for j in range(i + 1, len_centers):
            if euclidean(centers[i], centers[j]) < threshold:
                count += 1
    if count > int(person_count * cof):
        return True
    else:
        return False
def create_ellipse(center, axes):
    ellipse = Point(center).buffer(1)
    ellipse = scale(ellipse, axes[0], axes[1])
    return ellipse
def Abnormal_Detection(frame, draw_frame, cof):
    global width, height, fps, flags, Abnormal_count, abnormal_frame_count, avg_person_count
    frame_interval = int(fps)
    results, person_count, centers, boxes = detect_people(frame)
    if abnormal_frame_count % frame_interval == 0:
        Abnormal_count.append(person_count)
        if len(Abnormal_count) > fps * 5:
            Abnormal_count.pop(0)
        avg_person_count = np.mean(Abnormal_count)
    ellipses = []
    for result in results:
        for box in result.boxes:
            if box.cls.item() == 0:
                x1, y1, x2, y2 = map(int, box.xyxy[0])
                center_x = int((x1 + x2) / 2)
                cv2.line(draw_frame, (center_x, y1), (center_x, y2), (0, 255, 0), 2)
                major_axis = int(1 * (x2 - x1))
                minor_axis = int(0.6 * (x2 - x1))
                ellipses.append(((center_x, y2), (major_axis, minor_axis)))
    overlap_flags = [False] * len(ellipses)
    for i in range(len(ellipses)):
        ellipse1 = create_ellipse(ellipses[i][0], ellipses[i][1])
        for j in range(i + 1, len(ellipses)):
            ellipse2 = create_ellipse(ellipses[j][0], ellipses[j][1])
            if ellipse1.intersects(ellipse2):
                overlap_flags[i] = True
                overlap_flags[j] = True
    for i, ellipse in enumerate(ellipses):
        color = (0, 0, 255) if overlap_flags[i] else (0, 255, 0)
        center, axes = ellipse
        cv2.ellipse(draw_frame, center, axes, 0, 0, 360, color, 2)
    cv2.putText(draw_frame, f'Detected: {person_count}', (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 0, 255), 2, cv2.LINE_AA)
    cv2.putText(draw_frame, f'Avg (15s): {int(avg_person_count)}', (10, 60), cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 0, 255), 2,
               cv2.LINE_AA)
    if distance_cal(centers, person_count, cof) and person_count >= avg_person_count:
        cv2.putText(draw_frame, 'Crowding', (10, 90), cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 0, 255), 2, cv2.LINE_AA)
        flags['AbnormalEvents'] = 1
    else:
        cv2.putText(draw_frame, 'Not Crowding', (10, 90), cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 0, 255), 2, cv2.LINE_AA)
        flags['AbnormalEvents'] = 0
    abnormal_frame_count += 1
    AbnormalEvents_queue.append(flags['AbnormalEvents'])
    return draw_frame

def Violence_Detection(frame, draw_frame, cof):
    global flags
    results = model_Violence.predict(source=frame, classes=[1], verbose = False, conf=cof)
    boxes = results[0].boxes.xyxy.cpu()
    if len(boxes) > 0:
        flags['Violence'] = 1
        annotator = Annotator(draw_frame, line_width=2, example=str(model_Violence.model.names))
        for box in boxes:
            annotator.box_label(box, str(model_Violence.model.names[1]), color=colors(0, True))
    else:
        flags['Violence'] = 0
    Violence_queue.append(flags['Violence'])
    return draw_frame
def RolliongDoor_Detection(frame, draw_frame, cof):
    global prev_y2_sum, flags
    current_y2_sum = 0
    gate_polygon, current_box, draw_frame = detect_gate(frame, draw_frame, cof)  # 進鐵捲門偵測
    person_center, draw_frame = detect_person(frame, draw_frame, cof)  # 進人偵測
    if current_box is not None:
        current_y2 = current_box[3]
        y2_positions.append(current_y2)
        if len(y2_positions) == y2_positions.maxlen:
            temp = current_y2_sum
            current_y2_sum = sum(y2_positions)
            prev_y2_sum = temp
            y2_positions.clear()
        gate_closing = is_gate_closing(current_y2_sum, prev_y2_sum)  # 判斷是否正在關閉
        if gate_closing:
            if person_center and gate_polygon.contains(Point(person_center)):
                flags['RollingDoor'] = 1
                cv2.putText(frame, "Warning", (30, 155), cv2.FONT_HERSHEY_SIMPLEX, 2, (0, 0, 255), 3)
            draw_frame = cv2.polylines(img=frame, pts=[np.array(gate_polygon.exterior.coords, dtype=np.int32)],
                                  isClosed=True, color=(255, 0, 0), thickness=3)
        else:
            flags['RollingDoor'] = 0
    RollingDoor_queue.append(flags['RollingDoor'])
    return draw_frame
def is_gate_closing(current_y2_sum, prev_y2_sum):
    if prev_y2_sum is None:
        return False
    if abs(current_y2_sum - prev_y2_sum) > 5:
        return True
    else:
        return False
def Weapon_Detection(frame, draw_frame, cof, selected_weapon):
    global flags, class_name, detected_weapon, to_be_upload_type, weapon_type
    draw_frame = preprocess_frame(frame)
    selected_class = []
    # 根據使用者選擇設置需要檢測的類別索引
    if 'baseball-bat' in selected_weapon and 'knife' in selected_weapon:
        selected_class = [0, 1]
    elif 'knife' in selected_weapon:
        selected_class = [1]
    elif 'baseball-bat' in selected_weapon:
        selected_class = [0]

    # 執行檢測
    results = model_Weapon.predict(source=frame, verbose=False, conf=cof, classes=selected_class)
    # 提取檢測結果
    boxes = results[0].boxes.xyxy.cpu().numpy() if results[0].boxes.xyxy is not None else []
    clss = results[0].boxes.cls.cpu().tolist() if results[0].boxes.cls is not None else []
    confs = results[0].boxes.conf.cpu().tolist() if results[0].boxes.conf is not None else []
    # 初始化標誌
    flags['Weapon'] = 0
    # 如果有檢測到物件
    if len(boxes) > 0:
        flags['Weapon'] = 1  # 更新標誌
        annotator = Annotator(draw_frame, line_width=2, example=str(model_Weapon.model.names))
        for box, cls, conf in zip(boxes, clss, confs):
            # 獲取類別名稱
            class_name = model_Weapon.model.names[int(cls)]
            # 標註檢測結果
            label = f'{class_name} {conf:.2f}'
            annotator.box_label(box, label, color=colors(cls, True))
    else:
        flags['Weapon'] = 0
    # 更新檢測隊列
    Weapon_queue.append(flags['Weapon'])
    return draw_frame
def get_selected_weapons():
    return [key for key, var in weapon_items.items() if var.get()]
def check2(head_point, s_point):
    x_s, y_s = s_point
    x_h, y_h = head_point
    fin = abs(y_s - y_h) / abs(x_s - x_h)
    ang = math.atan(fin)
    angle = np.degrees(abs(ang))

    if angle <= 50:
        return 1
    else:
        return 0
def check3(height, width):
    if width/height > 1:
        return 1
    else:
        return 0
def Falling_Detection(frame, draw_frame, cof):
    global flags, fps, keep_frame, stay_frame
    skeleton = [[16, 14], [14, 12], [17, 15], [15, 13], [12, 13], [6, 12], [7, 13], [6, 7], [6, 8],
                [7, 9], [8, 10], [9, 11], [2, 3], [1, 2], [1, 3], [2, 4], [3, 5], [4, 6], [5, 7]]
    pose_palette = np.array([[255, 128, 0], [255, 153, 51], [255, 178, 102], [230, 230, 0], [255, 153, 255],
                             [153, 204, 255], [255, 102, 255], [255, 51, 255], [102, 178, 255], [51, 153, 255],
                             [255, 153, 153], [255, 102, 102], [255, 51, 51], [153, 255, 153], [102, 255, 102],
                             [51, 255, 51], [0, 255, 0], [0, 0, 255], [255, 0, 0], [255, 255, 255]], dtype=np.uint8)
    kpt_color = pose_palette[[16, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9, 9, 9]]
    limb_color = pose_palette[[9, 9, 9, 9, 7, 7, 7, 0, 0, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16]]

    og_frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
    frame = og_frame.copy()
    results = model_person_pose.predict(source=frame, verbose = False, conf=cof)[0]
    names = model_person_pose.model.names
    boxes = results.boxes.data.tolist()
    if len(boxes) == 0:
        flags['Falling'] = 0
        Falling_queue.append(flags['Falling'])
        return draw_frame
    keypoints = results.keypoints.cpu().numpy()
    K_num = 0
    for keypoint in keypoints.data:
        K_num += 1
        for i, (x, y, conf) in enumerate(keypoint):
            color_k = [int(x) for x in kpt_color[i]]
            if conf < cof:
                flags['Falling'] = 0
                continue
            if x != 0 and y != 0:
                cv2.circle(draw_frame, (int(x), int(y)), 5, color_k, -1, lineType=cv2.LINE_AA)
        for i, sk in enumerate(skeleton):
            pos1 = (int(keypoint[(sk[0] - 1), 0]), int(keypoint[(sk[0] - 1), 1]))
            pos2 = (int(keypoint[(sk[1] - 1), 0]), int(keypoint[(sk[1] - 1), 1]))
            conf1 = keypoint[(sk[0] - 1), 2]
            conf2 = keypoint[(sk[1] - 1), 2]
            if conf1 < cof or conf2 < cof:
                flags['Falling'] = 0
                continue
            if pos1[0] == 0 or pos1[1] == 0 or pos2[0] == 0 or pos2[1] == 0:
                flags['Falling'] = 0
                continue
            cv2.line(draw_frame, pos1, pos2, [int(x) for x in limb_color[i]], thickness=2, lineType=cv2.LINE_AA)
        if keypoint[15][2] >= cof and keypoint[16][2] >= cof:
            point_x = (keypoint[15][0] + keypoint[16][0]) / 2
            point_y = (keypoint[15][1] + keypoint[16][1]) / 2
            s_point = (point_x, point_y)
            if keypoint[0][2] >= cof:
                head_point = (keypoint[0][0], keypoint[0][1])
                flag[1] = check2(head_point, s_point)
            elif keypoint[1][2] >= cof:
                head_point = (keypoint[1][0], keypoint[1][1])
                flag[1] = check2(head_point, s_point)
            elif keypoint[2][2] >= cof:
                head_point = (keypoint[2][0], keypoint[2][1])
                flag[1] = check2(head_point, s_point)
            elif keypoint[3][2] >= cof:
                head_point = (keypoint[3][0], keypoint[3][1])
                flag[1] = check2(head_point, s_point)
            elif keypoint[4][2] >= cof:
                head_point = (keypoint[4][0], keypoint[4][1])
                flag[1] = check2(head_point, s_point)
    for obj in boxes:
        left, top, right, bottom = int(obj[0]), int(obj[1]), int(obj[2]), int(obj[3])
        confidence = obj[4]
        label = int(obj[5])
        if label == 0 and confidence >= cof:
            color = (255,0,0)
            if keep_frame >= int(fps * waiting_second):
                color = (0,0,255)
            cv2.rectangle(draw_frame, (left, top), (right, bottom), color=color, thickness=2, lineType=cv2.LINE_AA)
            caption = f"{names[label]} {confidence:.2f}"
            w, h = cv2.getTextSize(caption, 0, 1, 2)[0]
            cv2.rectangle(draw_frame, (left - 3, top - 33), (left + w + 10, top), color, -1)
            cv2.putText(draw_frame, caption, (left, top - 5), 0, 1, (0, 0, 0), 2, 16)
            # detect
            width = abs(right - left)
            height = abs(top - bottom)
            flag[2] = check3(height, width)
    if flag[1] == 1 and flag[2] == 1:
        cv2.rectangle(draw_frame, (10, 30), (10, 30), (0, 0, 255), -1)
        keep_frame += 1
        if keep_frame >= int(fps * waiting_second):
            flags['Falling'] = 1
            cv2.putText(draw_frame, f"FALLING !", (30, 150), 0, 2, (0, 0, 255), 2, 16)
            stay_frame = 0
    elif keep_frame >= int(fps * waiting_second) and stay_frame <= int(fps * stay_second):
        stay_frame += 1
        cv2.putText(draw_frame, f"FALLING !", (30, 150), 0, 2, (0, 0, 255), 2, 16)
    else:
        flags['Falling'] = 0
        keep_frame = 0
        stay_frame += 1
    Falling_queue.append(flags['Falling'])
    return draw_frame
def ElectronicFence_Detection(frame, draw_frame, cof):
    global ElectronicFence_flag, flags
    coordinate = []
    results1 = model_cone.predict(source=frame, conf=cof, verbose=False)
    results2 = model_person.predict(source=frame, conf=cof, classes=[0], verbose=False)
    boxes1 = results1[0].boxes.xyxy.cpu()
    boxes2 = results2[0].boxes.xyxy.cpu()
    clss = results1[0].boxes.cls.cpu().tolist()
    if len(results1[0].boxes) <= 3:
        return draw_frame
    annotator = Annotator(draw_frame, line_width=2, example=str(model_person.model.names))
    for box, cls in zip(boxes1, clss):
        bbox_cone = ((box[0] + box[2]) / 2, (box[1] + box[3]) / 2)
        coordinate += [[int(bbox_cone[0]), int(bbox_cone[1])]]
    if len(coordinate) > 0:
        center = [sum(x[0] for x in coordinate) / len(coordinate), sum(x[1] for x in coordinate) / len(coordinate)]
        coordinate = sorted(coordinate, key=lambda x: get_polar_angle(x, center))
        counting_regions[0]["polygon"] = Polygon(coordinate)
    for box, cls in zip(boxes2, clss):
        bbox_person = ((box[0] + box[2]) / 2, (box[1] + 3*box[3]) / 4 )
        annotator.box_label(box, str(model_person.model.names[cls]), color=colors(cls, True))
        for region in counting_regions:
            if region["polygon"].contains(Point((bbox_person[0], bbox_person[1]))):
                flags['ElectronicFence'] = 1
                cv2.putText(draw_frame, "Warning", (30, 155), cv2.FONT_HERSHEY_SIMPLEX, 2, (0, 0, 255), 3)
            else:
                flags['ElectronicFence'] = 0
    if flags['ElectronicFence'] == 1:
        draw_frame = cv2.polylines(img=draw_frame, pts=[np.array(coordinate)], isClosed=True, color=(0, 0, 255), thickness=4)
    elif flags['ElectronicFence'] == 0:
        draw_frame = cv2.polylines(img=draw_frame, pts=[np.array(coordinate)], isClosed=True, color=(0, 255, 0), thickness=4)
    ElectronicFence_queue.append(flags['ElectronicFence'])
    return draw_frame

def start_recording_if_needed(frame_count, detected_frame, event_name="event"):
    global recording, start_index, out, save_path, fps, out_path

    if not recording:
        # 初始化錄影參數
        frame_height, frame_width, _ = detected_frame.shape
        output_name = f"{event_name}_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.mp4"
        out_path = os.path.join(save_path, output_name)
        fourcc = cv2.VideoWriter_fourcc(*'mp4v')  # 選擇 mp4 編碼格式
        out = cv2.VideoWriter(out_path, fourcc, fps, (frame_width, frame_height))
        # 設置錄影開始的標記
        start_index = frame_count
        recording = True
# Show_frame is to show the processed frame
def show_frame():
    global processed_frame, a, current_frame, check_queues, abnormal_frame_count, Abnormal_count, uploading_window, out_path, video_url, event_types_str, image_url, current_frame, total_frames, frame_count, Frame_right, Frame6, canvas, frame_queue2, Violence_queue, out, recording
    # print(f'to_be_upload_type: {to_be_upload_type}')
    coordinate = []  # 視情況設定多邊形頂點
    if video_url and image_url:
        if to_be_upload_type:
            event_types_str = ', '.join(to_be_upload_type)
            send_video_and_image(video_url, full_path)
            log_event(event_types_str, 'undefined')
            uploading_window.destroy()
            a = 0
            to_be_upload_type.clear()
    if frame_queue2:
        detected_frame = frame_queue2.popleft()  # 取得已處理的幀
        for name, queue in check_queues.items():
            if queue and frame_count < len(queue):
                if queue[frame_count] == 1:
                    if name not in to_be_upload_type:
                        to_be_upload_type.append(name)
                    if not recording:
                        save_frame_as_image(detected_frame)
                        add_history(get_latest_ID() + 1, to_be_upload_type)
                        start_recording_if_needed(frame_count, detected_frame, event_name=name)
        if recording:
            out.write(detected_frame)
            if frame_count - start_index + 1 >= total_frames:
                recording = False
                out.release()
                uploading()
                root.update_idletasks()
                upload_video_to_imgur(out_path)
                upload_image_to_imgur()

        to_show_frame = cv2.polylines(img=detected_frame, pts=[np.array(coordinate)], isClosed=True, color=(0, 255, 0), thickness=4)
        processed_frame = to_show_frame.copy()  # 備份當前幀
        current_frame += 1  # 更新幀數
        # 轉換幀和調整大小
        display_frame(to_show_frame)
        frame_count += 1
        root.after(2, show_frame)

    elif not frame_queue2:  # 確保 frame_queue2 為空時停止錄影
        print(f'video over')
        if recording:
            recording = False
            out.release()
            uploading()
            upload_video_to_imgur(out_path)
            upload_image_to_imgur()

            if video_url and image_url:
                if to_be_upload_type:
                    event_types_str = ', '.join(to_be_upload_type)
                    send_video_and_image(video_url, full_path)
                    log_event(event_types_str, 'undefined')
                    uploading_window.destroy()
                    a = 0
                    to_be_upload_type.clear()
        total_frames = 0
        current_frame = 0
        Abnormal_count = []
        abnormal_frame_count = 0
        print("Show_Frame end execute")
        cap.release()
        play_next_video()

def uploading():
    global uploading_window, upload_bar, upload_val, a
    print('uploading!!!!!!!!!!!!!!!')
    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()

    uploading_window_width = 350
    uploading_window_height = 125

    x = (screen_width - uploading_window_width) // 2
    y = (screen_height - uploading_window_height) // 2
    uploading_window = tk.Toplevel(root)
    uploading_window.geometry(f"{uploading_window_width}x{uploading_window_height}+{x}+{y}")
    tk.Label(uploading_window, text='Uploading...', font=('verdana', 12)).pack(pady=10)
    upload_bar = ttk.Progressbar(uploading_window, orient="horizontal", mode='determinate', length=300)
    upload_bar.pack(pady=10)
    a = 0
    upload_val = tk.StringVar()
    upload_val.set('0%')
    tk.Label(uploading_window, textvariable=upload_val, font=('verdana', 12)).pack(pady=10)
    uploading_window.update()

# 建立各個變數
Violence_var = BooleanVar()
audio_var = BooleanVar()
Weapon_var = BooleanVar()
knife_var = BooleanVar()
bat_var = BooleanVar()
RollingDoor_var = BooleanVar()
AbnormalEvents_var = BooleanVar()
ElectronicFence_var = BooleanVar()
Falling_var = BooleanVar()

# 儲存按鈕的變數與標籤的字典
button_vars = {
    'Violence': Violence_var,
    'Audio': audio_var,
    'Weapon': Weapon_var,
    'RollingDoor': RollingDoor_var,
    'AbnormalEvents': AbnormalEvents_var,
    'ElectronicFence': ElectronicFence_var,
    'Falling': Falling_var
}
weapon_items = {
    'knife': knife_var,
    'baseball-bat': bat_var
}
def on_Weapon_toggle():
    if Weapon_var.get():
        knife_var.set(True)
        bat_var.set(True)
    else:
        knife_var.set(False)
        bat_var.set(False)
def change_mode_By_Sound(detect_words):
    if "開啟" in detect_words:
        if "暴力" in detect_words:
            Violence_var.set(True)
        if "危險物" in detect_words:
            Weapon_var.set(True)
        if "鐵捲門" in detect_words:
            RollingDoor_var.set(True)
        if "異常事件" in detect_words:
            AbnormalEvents_var.set(True)
        if "圍籬" in detect_words:
            ElectronicFence_var.set(True)
        if "跌倒" in detect_words:
            Falling_var.set(True)
    elif "關閉" in detect_words:
        if "暴力" in detect_words:
            Violence_var.set(False)
        if "危險物" in detect_words:
            Weapon_var.set(False)
        if "鐵捲門" in detect_words:
            RollingDoor_var.set(False)
        if "異常事件" in detect_words:
            AbnormalEvents_var.set(False)
        if "圍籬" in detect_words:
            ElectronicFence_var.set(False)
        if "跌倒" in detect_words:
            Falling_var.set(False)
def filter_By_Sound(detect_words):
    print("Here")
# 回呼函數，用於檢查所有按鈕的狀態
def on_button_toggle():
    pressed_buttons = []
    for button_name, var in button_vars.items():
        if var.get():  # 檢查變數的值是否為 True
            pressed_buttons.append(button_name)
    return pressed_buttons  # 確保回傳按下的按鈕

def time_format(old_time_str):
    # 使用正則表達式提取所有數字
    numbers = re.findall(r'\d+', old_time_str)

    # 構建新的時間格式
    if len(numbers) >= 6:
        new_time_str = f"{numbers[0]}{numbers[1]}{numbers[2]}_{numbers[3]}{numbers[4]}{numbers[5]}"
        return new_time_str
    else:
        raise ValueError("輸入的時間字符串格式不正確，無法提取完整的時間數據。")

def default_setting():
    global Violence_scale, Weapon_scale, RollingDoor_scale, AbnormalEvents_scale, ElectronicFence_scale, Falling_scale
    Violence_scale.set(0.8)
    Weapon_scale.set(0.3)
    RollingDoor_scale.set(0.7)
    AbnormalEvents_scale.set(0.5)
    ElectronicFence_scale.set(0.7)
    Falling_scale.set(0.7)
# 主內容框架
content_frame = tk.Frame(root, bg="white")
content_frame.pack(expand=1, fill="both")

# 配置 content_frame 的 grid 布局以允许扩展
content_frame.grid_rowconfigure(0, weight=3)

content_frame.grid_columnconfigure(1, weight=10)

# 创建 Frame_left
Frame_left = tk.Frame(content_frame, bd=5, relief=tk.GROOVE, bg='lightgray')
Frame_left.grid(row=0, column=0, sticky=tk.NSEW, padx=0, pady=5)

# 创建 Frame_right
Frame_right = tk.Frame(content_frame, bd=5, relief=tk.GROOVE, bg='lightgray')
Frame_right.grid(row=0, column=1, sticky=tk.NSEW, padx=0, pady=5)

# 在 Frame_left 中创建四个 Frame
Frame1 = tk.Frame(Frame_left, pady=10, padx=10, bg='lightgray')
Frame1.pack(pady=5)

Frame2 = tk.Frame(Frame_left, padx=5, pady=5, bg='lightgray')
Frame2.pack(pady=5)

Frame3 = tk.Frame(Frame_left, padx=5, pady=5, bg='lightgray')
Frame3.pack(pady=5)

Frame4 = tk.Frame(Frame_left, pady=10, padx=5)
Frame4.pack(pady=5, fill='y', expand=True)

time_label = tk.Label(Frame1, text='', font=('Verdana', 12), bg='lightgray')
time_label.pack(side='left', padx=10)

tk.Button(Frame1, text='Default', font=('Verdana', 12), command=default_setting).pack(side='right', padx=10)
# 建立 GUI 元件
Violence_rounded_label, Violence_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Violence_rounded_label.grid(row=0, column=0, sticky='w', pady=5, padx=20)
Violence_check = ttk.Checkbutton(Violence_rounded_frame, var=Violence_var, style="Switch.TCheckbutton")
Violence_check.pack(side='left')
Violence_label = tk.Label(Violence_rounded_frame, text='Violence', font=('Verdana', 13))
Violence_label.pack(side='left', padx=(10, 0))

Weapon_rounded_label, Weapon_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Weapon_rounded_label.grid(row=2, column=0, sticky='w', pady=5, padx=20)
Weapon_check = ttk.Checkbutton(Weapon_rounded_frame, var=Weapon_var, style="Switch.TCheckbutton")
Weapon_check.pack(side='left')
Weapon_label = tk.Label(Weapon_rounded_frame, text='Weapon', font=('Verdana', 13))
Weapon_label.pack(side='left', padx=(10, 0))

WeaponOption_frame = tk.Frame(Frame2, bg='lightgray')
WeaponOption_frame.grid(row=3, column=0, sticky='w', pady=5)
knife_check = ttk.Checkbutton(WeaponOption_frame, var=knife_var, text='Knife')
knife_check.pack(side='left', padx=(50, 10))
bat_check = ttk.Checkbutton(WeaponOption_frame, var=bat_var, text='Bat')
bat_check.pack(side='left', padx=(10, 0))

Weapon_bar_label, Weapon_bar_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Weapon_bar_label.grid(row=2, column=1, sticky='e', padx=20, pady=5)
w_scale_value = tk.Label(Weapon_bar_frame, text='Conf                0.1', font=('verdana', 12))
w_scale_value.pack(side='top')
Weapon_scale = ttk.Scale(Weapon_bar_frame, from_=0.1, to=1.0, orient='horizontal', command=update_w_value)
Weapon_scale.pack(fill='x')

RollingDoor_rounded_label, RollingDoor_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
RollingDoor_rounded_label.grid(row=4, column=0, sticky='w', pady=5, padx=20)
RollingDoor_check = ttk.Checkbutton(RollingDoor_rounded_frame, var=RollingDoor_var, style="Switch.TCheckbutton")
RollingDoor_check.pack(side='left')
RollingDoor_label = tk.Label(RollingDoor_rounded_frame, text='Rolling Door', font=('Verdana', 13))
RollingDoor_label.pack(side='left', padx=(10, 0))

AbnormalEvents_rounded_label, AbnormalEvents_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
AbnormalEvents_rounded_label.grid(row=5, column=0, sticky='w', pady=5, padx=20)
AbnormalEvents_check = ttk.Checkbutton(AbnormalEvents_rounded_frame, var=AbnormalEvents_var, style="Switch.TCheckbutton")
AbnormalEvents_check.pack(side='left')
AbnormalEvents_label = tk.Label(AbnormalEvents_rounded_frame, text='Abnormal Events', font=('Verdana', 13))
AbnormalEvents_label.pack(side='left', padx=(10, 0))

ElectronicFence_rounded_label, ElectronicFence_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
ElectronicFence_rounded_label.grid(row=6, column=0, sticky='w', pady=5, padx=20)
ElectronicFence_check = ttk.Checkbutton(ElectronicFence_rounded_frame, var=ElectronicFence_var, style="Switch.TCheckbutton")
ElectronicFence_check.pack(side='left')
ElectronicFence_label = tk.Label(ElectronicFence_rounded_frame, text='Electronic Fence', font=('Verdana', 13))
ElectronicFence_label.pack(side='left', padx=(10, 0))

Falling_rounded_label, Falling_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Falling_rounded_label.grid(row=7, column=0, sticky='w', pady=5, padx=20)
Falling_check = ttk.Checkbutton(Falling_rounded_frame, var=Falling_var, style="Switch.TCheckbutton")
Falling_check.pack(side='left')
Falling_label = tk.Label(Falling_rounded_frame, text='Falling', font=('Verdana', 13))
Falling_label.pack(side='left', padx=(10, 0))

Violence_bar_label, Violence_bar_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Violence_bar_label.grid(row=0, column=1, sticky='e', padx=20, pady=5)
v_scale_value = tk.Label(Violence_bar_frame, text='Conf                0.1', font=('verdana', 12))
v_scale_value.pack(side='top')
Violence_scale = ttk.Scale(Violence_bar_frame, from_=0.1, to=1.0, orient='horizontal', command=update_v_value)
Violence_scale.pack(fill='x')

Weapon_rounded_label, Weapon_rounded_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Weapon_rounded_label.grid(row=2, column=0, sticky='w', pady=5, padx=20)
Weapon_check = ttk.Checkbutton(Weapon_rounded_frame, var=Weapon_var, style="Switch.TCheckbutton", command=on_Weapon_toggle)
Weapon_check.pack(side='left')
Weapon_label = tk.Label(Weapon_rounded_frame, text='Weapon', font=('Verdana', 13))
Weapon_label.pack(side='left', padx=(10, 0))

RollingDoor_bar_label, RollingDoor_bar_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
RollingDoor_bar_label.grid(row=4, column=1, sticky='e', padx=20, pady=5)
d_scale_value = tk.Label(RollingDoor_bar_frame, text='Conf                0.1', font=('verdana', 12))
d_scale_value.pack(side='top')
RollingDoor_scale = ttk.Scale(RollingDoor_bar_frame, from_=0.1, to=1.0, orient='horizontal', command=update_d_value)
RollingDoor_scale.pack(fill='x')

AbnormalEvents_bar_label, AbnormalEvents_bar_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
AbnormalEvents_bar_label.grid(row=5, column=1, sticky='e', padx=20, pady=5)
g_scale_value = tk.Label(AbnormalEvents_bar_frame, text='Conf                0.1', font=('verdana', 12))
g_scale_value.pack(side='top')
AbnormalEvents_scale = ttk.Scale(AbnormalEvents_bar_frame, from_=0.1, to=1.5, orient='horizontal', command=update_g_value)
AbnormalEvents_scale.pack(fill='x')

ElectronicFence_bar_label, ElectronicFence_bar_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
ElectronicFence_bar_label.grid(row=6, column=1, sticky='e', padx=20, pady=5)
e_scale_value = tk.Label(ElectronicFence_bar_frame, text='Conf                0.1', font=('verdana', 12))
e_scale_value.pack(side='top')
ElectronicFence_scale = ttk.Scale(ElectronicFence_bar_frame, from_=0.1, to=1.0, orient='horizontal', command=update_e_value)
ElectronicFence_scale.pack(fill='x')

Falling_bar_label, Falling_bar_frame = create_rounded_frame(Frame2, 250, 50, 20, 'white', bg_color='lightgray')
Falling_bar_label.grid(row=7, column=1, sticky='e', padx=20, pady=5)
f_scale_value = tk.Label(Falling_bar_frame, text='Conf                0.1', font=('verdana', 12))
f_scale_value.pack(side='top')
Falling_scale = ttk.Scale(Falling_bar_frame, from_=0.1, to=1.0, orient='horizontal', command=update_f_value)
Falling_scale.pack(fill='x')

red_image = Image.open("red_dot-removebg-preview.png").resize((20, 20))
tk_red = ImageTk.PhotoImage(red_image)
red_label = tk.Label(Frame3, image=tk_red, text=' Critical Risk', font=('verdana', 12), compound='left', bg='lightgray')
red_label.grid(row=0, column=0, padx=5)

orange_image = Image.open("orange-removebg-preview.png").resize((20, 20))
tk_orange = ImageTk.PhotoImage(orange_image)
orange_label = tk.Label(Frame3, image=tk_orange, text=' Dangerous', font=('verdana', 12), compound='left', bg='lightgray')
orange_label.grid(row=0, column=1, padx=5)

yellow_image = Image.open("yello-removebg-preview.png").resize((20, 20))
tk_yellow = ImageTk.PhotoImage(yellow_image)
yellow_label = tk.Label(Frame3, image=tk_yellow, text=' Medium Risk', font=('verdana', 12), compound='left', bg='lightgray')
yellow_label.grid(row=0, column=2, padx=5)

green_image = Image.open("green_dot-removebg-preview.png").resize((20, 20))
tk_green = ImageTk.PhotoImage(green_image)
green_label = tk.Label(Frame3, image=tk_green, text=' Low Risk', font=('verdana', 12), compound='left', bg='lightgray')
green_label.grid(row=0, column=3, padx=5)

tree_scrollbar = tk.Scrollbar(Frame4, orient="vertical")
tree_scrollbar.pack(side='right', fill='y')

history = ttk.Treeview(Frame4, columns=("ID", "Event", "Time"), show='headings', yscrollcommand=tree_scrollbar.set)

history.heading("ID", text="ID")
history.heading("Event", text="Event")
history.heading("Time", text="Time")


history.pack(fill='both', expand=True)

tree_scrollbar.config(command=history.yview)


history.bind("<ButtonRelease-1>", classify)

Frame5 = tk.Frame(Frame_right, padx=10, pady=10, relief=tk.GROOVE, bd=3)
Frame5.grid(row=0, column=0, padx=10, pady=10, sticky='ew')

canvas = tk.Canvas(Frame_right, bd=2, relief=tk.GROOVE, bg='black')
canvas.grid(row=1, column=0, padx=10, pady=10, sticky='nsew')

Frame6 = tk.Frame(Frame_right, relief=tk.GROOVE, bd=3)
Frame6.grid(row=2, column=0, padx=10, pady=10, sticky='ew')

Frame_right.grid_rowconfigure(0, weight=0)  # Frame5 不擴展
Frame_right.grid_rowconfigure(1, weight=1)  # canvas 擴展
Frame_right.grid_rowconfigure(2, weight=0)  # Frame6 不擴展
Frame_right.grid_columnconfigure(0, weight=1)

Frame5.grid_columnconfigure(0, weight=0)
Frame5.grid_columnconfigure(1, weight=1)
Frame5.grid_columnconfigure(2, weight=1)

Frame6.grid_columnconfigure(0, weight=1)
Frame6.grid_columnconfigure(1, weight=2)
Frame6.grid_columnconfigure(2, weight=1)

Frame7 = tk.Frame(Frame6, pady=5)
Frame7.pack(fill='x', expand=True)

event_list_button = tk.Button(Frame7, text='Event List', font=('Verdana', 12, 'bold'), command=show_all_event)
event_list_button.pack(side='left', padx=(10, 10), pady=5)

now_playing_label = tk.Label(Frame7, text='', font=('Verdana', 12, 'bold'))
now_playing_label.pack(side='left', padx=(10, 10), expand=True, fill='x', pady=5)

import_video_button = tk.Button(Frame5, text='Import Video', font=('Verdana', 12, 'bold'), command=lambda: choose_import_video())
import_video_button.grid(row=0, column=1, padx=10, pady=5, sticky='w')

import_path_label = tk.Label(Frame5, text='', font=('Verdana', 12, 'bold'))
import_path_label.grid(row=0, column=2, padx=10, pady=5, sticky='w')

save_path_button = tk.Button(Frame5, text='Save Video', font=('Verdana', 12, 'bold'), command=lambda: choose_save_location())
save_path_button.grid(row=1, column=1, padx=10, pady=5, sticky='w')

sound_recog_img = Image.open("microphone.png").resize((30,30))
sound_recog_TK = ImageTk.PhotoImage(sound_recog_img)
sound_recog = tk.Button(Frame5, image=sound_recog_TK, command=create_sound_recog_window)
sound_recog.grid(row=0, column=0, rowspan=2, columnspan=1, padx=10)

save_path_label = tk.Label(Frame5, text='', font=('Verdana', 12, 'bold'))
save_path_label.grid(row=1, column=2, padx=10, pady=5, sticky='w')


Frame_right.update_idletasks()  #刷新
canvas.configure(height=Frame_right.winfo_height() - Frame5.winfo_height() - Frame6.winfo_height() - 40)  # 40 是上下 padding 的總和

video = None
video_path = None
update_time()
sv_ttk.set_theme("light")
default_setting()
root.mainloop()
