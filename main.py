"""
╔══════════════════════════════════════════════════════════════════════════════╗
║   ETLAB PRO — YOUR ATTENDANCE BUDDY 🎓                                     ║
║   v4.0 | Playwright-powered | Bulletproof | Full Analytics                  ║
║   "know before you yolo the bunk" — the only attendance tool you need       ║
╠══════════════════════════════════════════════════════════════════════════════╣
║  FIXED IN v4.0:                                                              ║
║   • Attendance subject page: pivot table parser (was reading roll no         ║
║     UKP25CD030 as a subject with 381 classes — now correctly reads all       ║
║     10 subjects from the wide-format table with present/total/%  per col)    ║
║   • Results page: each widget-box section (Sessional, Module Test,           ║
║     Assignments, Tutorials, Seminars) parsed separately with correct          ║
║     column mapping — Maximum Marks / Marks Obtained no longer swapped        ║
║   • batch_id discovery: now prefers long encoded IDs (32481378255) from      ║
║     href patterns over short numeric IDs to avoid collision with student ID  ║
║   • Subject name enrichment: codes from attendance table resolved to full    ║
║     names via results data                                                    ║
║   • Table formatter: max col width reduced, long subjects truncated cleanly  ║
║   • Profile parser: now pulls Roll No from the attendance subject table      ║
║   • Overall % now uses effective_present not just present                    ║
║   • Duty leave and medical leave properly reflected in summary stats         ║
║   • What-if simulator: works by subject code prefix too                      ║
║   • New: per-subject series marks table with exam-wise breakdown             ║
║   • New: risk prioritisation with weeks-to-safe calculation                  ║
║   • New: attendance heatmap ASCII calendar per subject                       ║
║   • New: --semester flag to switch semester without editing code             ║
║   • New: graceful empty-table handling in results (no junk rows)             ║
╚══════════════════════════════════════════════════════════════════════════════╝

INSTALL:
  pip install playwright beautifulsoup4 pandas numpy matplotlib seaborn lxml
  playwright install chromium
"""

# ─────────────────────────────────────────────────────────────────────────────
# IMPORTS
# ─────────────────────────────────────────────────────────────────────────────

import os
import re
import sys
import json
import time
import math
import heapq
import hashlib
import argparse
import textwrap
import traceback
import threading
import copy
import calendar as cal_module
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional, Dict, List, Tuple, Any
from dataclasses import dataclass, field, asdict
from collections import defaultdict, OrderedDict, deque
from urllib.parse import urljoin
from enum import Enum

import warnings
warnings.filterwarnings("ignore")

# ── optional heavy deps ───────────────────────────────────────────────────────

try:
    from playwright.sync_api import (
        sync_playwright, Page, Browser, BrowserContext,
        Response as PWResponse,
    )
    PLAYWRIGHT_OK = True
except ImportError:
    PLAYWRIGHT_OK = False
    print("⚠️  playwright not found. Run: pip install playwright && playwright install chromium")

try:
    from bs4 import BeautifulSoup, Tag, NavigableString
    BS4_OK = True
except ImportError:
    BS4_OK = False
    print("⚠️  beautifulsoup4 not found. Run: pip install beautifulsoup4 lxml")

try:
    import pandas as pd
    import numpy as np
    PANDAS_OK = True
except ImportError:
    PANDAS_OK = False

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.gridspec as gridspec
    MATPLOTLIB_OK = True
except ImportError:
    MATPLOTLIB_OK = False

try:
    from scipy import stats as scipy_stats
    SCIPY_OK = True
except ImportError:
    SCIPY_OK = False


# ─────────────────────────────────────────────────────────────────────────────
# ANSI COLORS
# ─────────────────────────────────────────────────────────────────────────────

class C:
    """ANSI color codes. Auto-disabled on non-TTY."""
    _ok = sys.stdout.isatty()

    RESET    = "\033[0m"   if _ok else ""
    BOLD     = "\033[1m"   if _ok else ""
    DIM      = "\033[2m"   if _ok else ""
    BRED     = "\033[91m"  if _ok else ""
    BGREEN   = "\033[92m"  if _ok else ""
    BYELLOW  = "\033[93m"  if _ok else ""
    BBLUE    = "\033[94m"  if _ok else ""
    BMAGENTA = "\033[95m"  if _ok else ""
    BCYAN    = "\033[96m"  if _ok else ""

    @staticmethod
    def wrap(text: str, *codes: str) -> str:
        return "".join(codes) + str(text) + C.RESET

    @staticmethod
    def green(t):   return C.wrap(t, C.BGREEN)
    @staticmethod
    def red(t):     return C.wrap(t, C.BRED)
    @staticmethod
    def yellow(t):  return C.wrap(t, C.BYELLOW)
    @staticmethod
    def cyan(t):    return C.wrap(t, C.BCYAN)
    @staticmethod
    def magenta(t): return C.wrap(t, C.BMAGENTA)
    @staticmethod
    def bold(t):    return C.wrap(t, C.BOLD)
    @staticmethod
    def dim(t):     return C.wrap(t, C.DIM)
    @staticmethod
    def blue(t):    return C.wrap(t, C.BBLUE)


def _strip_ansi(s: str) -> str:
    return re.sub(r'\033\[[0-9;]*m', '', s)


def _box(lines: List[str], title: str = "", width: int = 72, color=None) -> str:
    """Draw a Unicode box around lines."""
    color = color or C.BCYAN
    inner = width - 2
    top    = f"{color}╔{'═' * inner}╗{C.RESET}"
    bottom = f"{color}╚{'═' * inner}╝{C.RESET}"
    result = [top]
    if title:
        padded = f" {title} ".center(inner)
        result.append(f"{color}║{C.BOLD}{padded}{C.RESET}{color}║{C.RESET}")
        result.append(f"{color}╠{'═' * inner}╣{C.RESET}")
    for line in lines:
        clean = _strip_ansi(line)
        pad = inner - len(clean)
        result.append(f"{color}║{C.RESET} {line}{' ' * max(0, pad - 1)}{color}║{C.RESET}")
    result.append(bottom)
    return "\n".join(result)


def _table(headers: List[str], rows: List[List[str]],
           col_widths: List[int] = None, max_col: int = 30) -> str:
    """Terminal table with capped column widths to avoid line-wrap chaos."""
    if not rows:
        return C.dim("  (no data)")

    if not col_widths:
        col_widths = []
        for i, h in enumerate(headers):
            max_w = len(_strip_ansi(h))
            for row in rows:
                if i < len(row):
                    max_w = max(max_w, len(_strip_ansi(str(row[i]))))
            col_widths.append(min(max_w + 2, max_col))

    def make_row(cells, sep="│", pad=" "):
        parts = []
        for i, cell in enumerate(cells):
            w   = col_widths[i] if i < len(col_widths) else 10
            cl  = len(_strip_ansi(str(cell)))
            pad_right = max(0, w - cl - 1)
            parts.append(f"{pad}{cell}{' ' * pad_right}")
        return sep + sep.join(parts) + sep

    sep_row  = "├" + "┼".join("─" * (w + 1) for w in col_widths) + "┤"
    top_line = "┌" + "┬".join("─" * (w + 1) for w in col_widths) + "┐"
    bot_line = "└" + "┴".join("─" * (w + 1) for w in col_widths) + "┘"

    colored_h = [C.bold(C.cyan(h)) for h in headers]
    lines = [top_line, make_row(colored_h), sep_row]
    for row in rows:
        lines.append(make_row([str(c) for c in row]))
    lines.append(bot_line)
    return "\n".join(lines)


def _progress_bar(value: float, width: int = 20, show_pct: bool = True) -> str:
    pct    = max(0.0, min(100.0, value))
    filled = int(width * pct / 100)
    empty  = width - filled
    color  = C.BGREEN if pct >= 75 else (C.BYELLOW if pct >= 60 else C.BRED)
    bar    = f"{color}{'█' * filled}{C.DIM}{'░' * empty}{C.RESET}"
    suffix = f" {color}{pct:.1f}%{C.RESET}" if show_pct else ""
    return f"[{bar}]{suffix}"


def _spinner(msg: str = "Loading"):
    frames = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
    stop   = threading.Event()

    def spin():
        i = 0
        while not stop.is_set():
            sys.stdout.write(f"\r{C.BCYAN}{frames[i % len(frames)]}{C.RESET} {msg}   ")
            sys.stdout.flush()
            time.sleep(0.1)
            i += 1
        sys.stdout.write("\r" + " " * (len(msg) + 10) + "\r")
        sys.stdout.flush()

    threading.Thread(target=spin, daemon=True).start()
    return stop


# ─────────────────────────────────────────────────────────────────────────────
# LOGGER
# ─────────────────────────────────────────────────────────────────────────────

class EtLabLogger:
    LEVELS = {"DEBUG": 0, "INFO": 1, "WARN": 2, "ERROR": 3, "CRITICAL": 4}

    def __init__(self, level: str = "INFO", log_file: Optional[Path] = None):
        self.level    = self.LEVELS.get(level.upper(), 1)
        self.log_file = log_file
        self._lock    = threading.Lock()
        if log_file:
            log_file.parent.mkdir(parents=True, exist_ok=True)
            log_file.write_text("", encoding="utf-8")   # fresh log each run

    def _write(self, level: str, emoji: str, color_fn, msg: str):
        if self.LEVELS.get(level, 0) < self.level:
            return
        ts   = datetime.now().strftime("%H:%M:%S")
        line = f"{C.dim(ts)} {color_fn(emoji + ' ' + msg)}"
        with self._lock:
            print(line)
            if self.log_file:
                clean = _strip_ansi(line)
                with open(self.log_file, "a", encoding="utf-8") as f:
                    f.write(clean + "\n")

    def debug(self, m):    self._write("DEBUG",    "🔍", C.dim,     m)
    def info(self, m):     self._write("INFO",     "ℹ️ ", C.cyan,    m)
    def success(self, m):  self._write("INFO",     "✅", C.green,   m)
    def warn(self, m):     self._write("WARN",     "⚠️ ", C.yellow,  m)
    def error(self, m):    self._write("ERROR",    "❌", C.red,     m)
    def critical(self, m): self._write("CRITICAL", "💀", C.red,     m)
    def vibe(self, m):     self._write("INFO",     "🔥", C.magenta, m)


# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────

BASE_URL         = "https://ukfcet.etlab.app"
OUTPUT_DIR       = Path("etlab_output")
CACHE_DIR        = OUTPUT_DIR / ".cache"
LOG_FILE         = OUTPUT_DIR / "etlab.log"
SAFE_THRESHOLD   = 75.0
DANGER_THRESHOLD = 60.0

# Non-subject column names in the pivot attendance table — skip these
ATTENDANCE_TABLE_SKIP_COLS = {
    "uni reg no", "unireg no", "reg no", "registration",
    "roll no", "rollno", "roll",
    "name", "student name",
    "total", "percentage", "%",
}

# Endpoint patterns tried in order — {batch_id} filled at runtime
ENDPOINT_PATTERNS: Dict[str, List[str]] = {
    "login":    ["/user/login"],
    "dashboard": ["/user/dashboard", "/dashboard", "/student/dashboard"],
    "profile":  ["/student/profile", "/ktuacademics/student/profile"],
    "attendance_date": [
        "/ktuacademics/student/attendance",
        "/student/attendance",
    ],
    "attendance_subject": [
        "/ktuacademics/student/viewattendancesubject/{batch_id}",
        "/student/viewattendancesubject/{batch_id}",
    ],
    "attendance_month": [
        "/ktuacademics/student/viewsubjectattendancemonth/{batch_id}",
    ],
    "results":   ["/student/results", "/ktuacademics/student/results"],
    "timetable": ["/student/timetable", "/ktuacademics/student/timetable"],
}

API_INTERCEPT_PATTERNS = [
    r"/api/", r"\.json", r"/attendance/data", r"format=json", r"type=json",
]

PRESENT_CLASSES = {"present", "att_present", "att-present", "p", "green", "success"}
ABSENT_CLASSES  = {"absent",  "att_absent",  "att-absent",  "a", "red",   "danger", "failure"}
DUTY_CLASSES    = {"duty", "duty_leave", "dutyleave", "dl", "yellow", "warning", "info"}
MEDICAL_CLASSES = {"medical", "medical_leave", "ml", "blue", "primary"}


# ─────────────────────────────────────────────────────────────────────────────
# DATA MODELS
# ─────────────────────────────────────────────────────────────────────────────

class AttendanceStatus(Enum):
    PRESENT    = "present"
    ABSENT     = "absent"
    DUTY_LEAVE = "duty_leave"
    MEDICAL    = "medical_leave"
    HOLIDAY    = "holiday"
    UNKNOWN    = "unknown"

    @classmethod
    def from_classes(cls, class_list: List[str]) -> "AttendanceStatus":
        combined = " ".join(class_list).lower()
        if any(c in combined for c in PRESENT_CLASSES):  return cls.PRESENT
        if any(c in combined for c in ABSENT_CLASSES):   return cls.ABSENT
        if any(c in combined for c in DUTY_CLASSES):     return cls.DUTY_LEAVE
        if any(c in combined for c in MEDICAL_CLASSES):  return cls.MEDICAL
        if "holiday" in combined:                        return cls.HOLIDAY
        return cls.UNKNOWN

    @property
    def counts_as_present(self) -> bool:
        return self in (self.PRESENT, self.DUTY_LEAVE, self.MEDICAL)

    @property
    def emoji(self) -> str:
        return {
            self.PRESENT:    "✅",
            self.ABSENT:     "❌",
            self.DUTY_LEAVE: "🟡",
            self.MEDICAL:    "🏥",
            self.HOLIDAY:    "🎉",
            self.UNKNOWN:    "❓",
        }[self]


@dataclass
class AttendanceRecord:
    date:         str
    day_of_week:  str
    subject_code: str
    subject_name: str
    status:       AttendanceStatus
    period:       int
    topic:        str = ""
    raw_class:    str = ""

    def to_dict(self) -> dict:
        d = asdict(self)
        d["status"] = self.status.value
        return d


@dataclass
class SubjectAttendance:
    """
    Full attendance analytics for one subject.

    Bunk budget formula:
      can_bunk:  floor((4P - 3T) / 3)   where P = effective_present, T = total
      need_more: ceil((0.75T - P) / 0.25)  when P/T < 0.75
    """
    code:          str
    name:          str
    total_classes: int = 0
    present:       int = 0
    absent:        int = 0
    duty_leave:    int = 0
    medical_leave: int = 0
    dates_present: List[str] = field(default_factory=list)
    dates_absent:  List[str] = field(default_factory=list)
    topics:        List[str] = field(default_factory=list)

    @property
    def effective_present(self) -> int:
        return self.present + self.duty_leave + self.medical_leave

    @property
    def percentage(self) -> float:
        if self.total_classes == 0:
            return 0.0
        return round(self.effective_present / self.total_classes * 100, 2)

    @property
    def raw_percentage(self) -> float:
        if self.total_classes == 0:
            return 0.0
        return round(self.present / self.total_classes * 100, 2)

    @property
    def is_safe(self) -> bool:
        return self.percentage >= SAFE_THRESHOLD

    @property
    def is_danger(self) -> bool:
        return self.percentage < DANGER_THRESHOLD

    @property
    def status_emoji(self) -> str:
        if self.is_safe:   return "✅"
        if self.is_danger: return "💀"
        return "⚠️"

    @property
    def classes_to_attend(self) -> int:
        if self.is_safe:
            return 0
        p = self.effective_present
        t = self.total_classes
        return max(0, math.ceil((0.75 * t - p) / 0.25))

    @property
    def classes_can_bunk(self) -> int:
        if not self.is_safe:
            return 0
        p = self.effective_present
        t = self.total_classes
        return max(0, math.floor((4 * p - 3 * t) / 3))

    @property
    def shortage(self) -> int:
        if self.is_safe:
            return 0
        return max(0, math.ceil(0.75 * self.total_classes) - self.effective_present)

    @property
    def vibe_check(self) -> str:
        pct = self.percentage
        if pct == 100:  return "absolutely unhinged nerd behavior 🤓"
        if pct >= 90:   return "professor's favorite fr fr 🏆"
        if pct >= 80:   return "solid, no cap ✨"
        if pct >= 75:   return f"safe but thin ice 🧊 ({self.classes_can_bunk} bunks left)"
        if pct >= 65:   return f"attend {self.classes_to_attend} more rn bestie ⚠️"
        if pct >= 50:   return "bro is cooked 💀 start attending"
        return              "detention speedrun any% 🚨"

    def predict_after_n_classes(self, n_total: int, n_attend: int) -> float:
        new_p = self.effective_present + n_attend
        new_t = self.total_classes + n_total
        return round(new_p / new_t * 100, 2) if new_t > 0 else 0.0

    def weeks_until_safe(self, classes_per_week: int = 6) -> Optional[int]:
        if self.is_safe:
            return 0
        if classes_per_week <= 0:
            return None
        return math.ceil(self.classes_to_attend / classes_per_week)

    def to_dict(self) -> dict:
        return {
            "code": self.code, "name": self.name,
            "total_classes": self.total_classes,
            "present": self.present, "absent": self.absent,
            "duty_leave": self.duty_leave, "medical_leave": self.medical_leave,
            "effective_present": self.effective_present,
            "percentage": self.percentage, "raw_percentage": self.raw_percentage,
            "is_safe": self.is_safe, "is_danger": self.is_danger,
            "classes_to_attend": self.classes_to_attend,
            "classes_can_bunk": self.classes_can_bunk,
            "shortage": self.shortage,
            "dates_present": self.dates_present,
            "dates_absent": self.dates_absent,
            "topics": self.topics, "vibe_check": self.vibe_check,
        }


@dataclass
class StudentProfile:
    name:          str = ""
    student_id:    str = ""
    roll_number:   str = ""
    reg_number:    str = ""        # UKP25CD030-style university reg no
    department:    str = ""
    semester:      str = ""
    batch:         str = ""
    college:       str = ""
    email:         str = ""
    phone:         str = ""
    batch_id:      str = ""
    student_db_id: str = ""

    @property
    def display_name(self) -> str:
        return self.name or self.student_id or "Unknown Student"


@dataclass
class SeriesExam:
    """One row from the sessional / module-test / assignment table."""
    category:        str   # "Sessional" | "Module Test" | "Assignment" | …
    subject_code:    str
    subject_name:    str
    semester:        str
    exam_label:      str   # "1", "2", "Assignment 1", …
    max_marks:       str
    marks_obtained:  str

    @property
    def percentage(self) -> Optional[float]:
        try:
            return round(float(self.marks_obtained) / float(self.max_marks) * 100, 1)
        except (ValueError, ZeroDivisionError):
            return None

    @property
    def is_submitted(self) -> bool:
        return self.marks_obtained.strip().upper() not in (
            "", "NOT SUBMITTED", "RESULTS NOT PUBLISHED", "N/A", "-"
        )


@dataclass
class TimetableSlot:
    day:          str
    period:       int
    subject_code: str
    subject_name: str
    start_time:   str = ""
    end_time:     str = ""


@dataclass
class ScrapedPage:
    url:        str
    html:       str
    fetched_at: str = field(default_factory=lambda: datetime.now().isoformat())
    method:     str = "playwright"
    status:     int = 200


@dataclass
class AcademicData:
    profile:            StudentProfile                = field(default_factory=StudentProfile)
    attendance_records: List[AttendanceRecord]        = field(default_factory=list)
    subject_attendance: Dict[str, SubjectAttendance]  = field(default_factory=dict)
    series_results:     List[SeriesExam]              = field(default_factory=list)
    timetable:          List[TimetableSlot]           = field(default_factory=list)
    scraped_pages:      Dict[str, ScrapedPage]        = field(default_factory=dict)
    api_data:           Dict[str, Any]                = field(default_factory=dict)
    scraped_at:         str                           = field(default_factory=lambda: datetime.now().isoformat())
    errors:             List[str]                     = field(default_factory=list)

    def add_error(self, msg: str):
        self.errors.append(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}")

    @property
    def has_attendance(self) -> bool:
        return bool(self.subject_attendance)

    @property
    def has_results(self) -> bool:
        return bool(self.series_results)


# ─────────────────────────────────────────────────────────────────────────────
# DSA UTILITIES
# ─────────────────────────────────────────────────────────────────────────────

class LRUCache:
    """O(1) get/put using OrderedDict."""
    def __init__(self, capacity: int = 100):
        self._cache: OrderedDict = OrderedDict()
        self._cap = capacity

    def get(self, key: str) -> Optional[Any]:
        if key not in self._cache:
            return None
        self._cache.move_to_end(key)
        return self._cache[key]

    def put(self, key: str, value: Any):
        if key in self._cache:
            self._cache.move_to_end(key)
        self._cache[key] = value
        if len(self._cache) > self._cap:
            self._cache.popitem(last=False)

    def __contains__(self, key):
        return key in self._cache


class Trie:
    """Prefix trie for fast subject lookup + Levenshtein fuzzy match."""
    def __init__(self):
        self._root: Dict = {}
        self._subjects: List[str] = []

    def insert(self, subject: str):
        node = self._root
        for ch in subject.upper():
            node = node.setdefault(ch, {})
        node["$"] = subject
        self._subjects.append(subject)

    def search_prefix(self, prefix: str) -> List[str]:
        node = self._root
        for ch in prefix.upper():
            if ch not in node:
                return []
            node = node[ch]
        return self._collect(node)

    def _collect(self, node: Dict) -> List[str]:
        res = []
        if "$" in node:
            res.append(node["$"])
        for k, child in node.items():
            if k != "$":
                res.extend(self._collect(child))
        return res

    def fuzzy_find(self, query: str, max_results: int = 5) -> List[Tuple[float, str]]:
        q = query.upper()
        scored = []
        for subject in self._subjects:
            s = subject.upper()
            dist = self._levenshtein(q, s[:len(q) + 5])
            prefix_score = len(os.path.commonprefix([q, s])) / max(len(q), 1)
            score = prefix_score - (dist / max(len(q), len(s), 1)) * 0.5
            scored.append((score, subject))
        scored.sort(reverse=True)
        return scored[:max_results]

    @staticmethod
    def _levenshtein(a: str, b: str) -> int:
        m, n = len(a), len(b)
        dp = list(range(n + 1))
        for i in range(1, m + 1):
            prev = dp[:]
            dp[0] = i
            for j in range(1, n + 1):
                cost = 0 if a[i - 1] == b[j - 1] else 1
                dp[j] = min(dp[j] + 1, dp[j - 1] + 1, prev[j - 1] + cost)
        return dp[n]


class MinHeap:
    """Min-heap for priority queue operations."""
    def __init__(self):
        self._heap: List[Tuple] = []

    def push(self, priority: float, item: Any):
        heapq.heappush(self._heap, (priority, id(item), item))

    def pop(self) -> Tuple[float, Any]:
        priority, _, item = heapq.heappop(self._heap)
        return priority, item

    def __len__(self):
        return len(self._heap)

    def to_sorted_list(self) -> List[Tuple[float, Any]]:
        return [(p, item) for p, _, item in sorted(self._heap)]


class RingBuffer:
    """Fixed-size circular buffer for streak tracking."""
    def __init__(self, size: int):
        self._buf: List[Optional[Any]] = [None] * size
        self._size = size
        self._pos  = 0
        self._count = 0

    def append(self, item: Any):
        self._buf[self._pos % self._size] = item
        self._pos  += 1
        self._count = min(self._count + 1, self._size)

    def to_list(self) -> List[Any]:
        if self._count < self._size:
            return [x for x in self._buf[: self._count] if x is not None]
        start = self._pos % self._size
        return self._buf[start:] + self._buf[:start]

    @property
    def current_streak(self) -> int:
        """Consecutive PRESENT count from most recent."""
        count = 0
        for item in reversed(self.to_list()):
            if item == AttendanceStatus.PRESENT:
                count += 1
            else:
                break
        return count


# ─────────────────────────────────────────────────────────────────────────────
# CACHE MANAGER
# ─────────────────────────────────────────────────────────────────────────────

class CacheManager:
    """Two-level cache: LRU memory + JSON disk.  Invalidates daily."""
    def __init__(self, cache_dir: Path, ttl_hours: int = 6):
        self._dir = cache_dir
        self._ttl = timedelta(hours=ttl_hours)
        self._mem = LRUCache(capacity=100)
        self._dir.mkdir(parents=True, exist_ok=True)

    def _key(self, url: str) -> str:
        day = datetime.now().strftime("%Y-%m-%d")
        return hashlib.sha256(f"{url}:{day}".encode()).hexdigest()[:16]

    def get(self, url: str) -> Optional[str]:
        key = self._key(url)
        cached = self._mem.get(key)
        if cached:
            return cached
        p = self._dir / f"{key}.json"
        if p.exists():
            try:
                data = json.loads(p.read_text())
                stored = datetime.fromisoformat(data["stored_at"])
                if datetime.now() - stored < self._ttl:
                    self._mem.put(key, data["html"])
                    return data["html"]
            except Exception:
                pass
        return None

    def set(self, url: str, html: str):
        key = self._key(url)
        self._mem.put(key, html)
        p = self._dir / f"{key}.json"
        try:
            p.write_text(json.dumps({"html": html, "stored_at": datetime.now().isoformat()}))
        except Exception:
            pass

    def clear(self):
        for f in self._dir.glob("*.json"):
            f.unlink(missing_ok=True)
        self._mem = LRUCache()


# ─────────────────────────────────────────────────────────────────────────────
# PLAYWRIGHT ENGINE
# ─────────────────────────────────────────────────────────────────────────────

class PlaywrightEngine:
    """
    Real Chromium browser via Playwright.
    • Intercepts JSON API responses automatically
    • Anti-bot-detection init script
    • Retry with exponential backoff
    • Caches pages (disk + memory) to avoid re-fetching on re-runs
    """

    def __init__(self, log: EtLabLogger, headless: bool = True, slow_mo: int = 0):
        self.log      = log
        self.headless = headless
        self.slow_mo  = slow_mo
        self._pw      = None
        self._browser: Optional[Browser]        = None
        self._context: Optional[BrowserContext] = None
        self._page:    Optional[Page]           = None
        self._intercepted: Dict[str, Any]       = {}
        self._cache   = CacheManager(CACHE_DIR)

    def start(self):
        if not PLAYWRIGHT_OK:
            raise RuntimeError("Playwright not installed.")
        self.log.info("Launching browser engine 🚀")
        self._pw      = sync_playwright().start()
        self._browser = self._pw.chromium.launch(
            headless=self.headless,
            slow_mo=self.slow_mo,
            args=[
                "--no-sandbox",
                "--disable-blink-features=AutomationControlled",
                "--disable-dev-shm-usage",
            ],
        )
        self._context = self._browser.new_context(
            viewport={"width": 1366, "height": 768},
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ),
            locale="en-IN",
            timezone_id="Asia/Kolkata",
            java_script_enabled=True,
            ignore_https_errors=True,
        )
        self._context.add_init_script(
            "Object.defineProperty(navigator,'webdriver',{get:()=>undefined});"
            "Object.defineProperty(navigator,'plugins',{get:()=>[1,2,3,4,5]});"
        )
        self._page = self._context.new_page()
        self._setup_intercept()
        self.log.success("Browser ready")

    def _setup_intercept(self):
        def on_response(resp: PWResponse):
            try:
                ct  = resp.headers.get("content-type", "")
                url = resp.url
                if "json" in ct or any(re.search(p, url) for p in API_INTERCEPT_PATTERNS):
                    try:
                        self._intercepted[url] = resp.json()
                        self.log.debug(f"API intercepted: {url[:80]}")
                    except Exception:
                        pass
            except Exception:
                pass
        self._page.on("response", on_response)

    def stop(self):
        for obj in [self._context, self._browser, self._pw]:
            try:
                if obj:
                    obj.close() if hasattr(obj, "close") else obj.stop()
            except Exception:
                pass

    def navigate(self, url: str, wait: str = "networkidle",
                 timeout: int = 30000, retries: int = 3) -> Optional[str]:
        cached = self._cache.get(url)
        if cached:
            self.log.debug(f"Cache hit: {url[:60]}")
            return cached

        strategies = [wait, "domcontentloaded", "load"]
        for attempt in range(retries):
            for strategy in strategies:
                try:
                    self._page.goto(url, wait_until=strategy, timeout=timeout)
                    self._page.wait_for_timeout(1200)
                    html = self._page.content()
                    if html and len(html) > 500:
                        self._cache.set(url, html)
                        return html
                except Exception as e:
                    if attempt == retries - 1:
                        self.log.warn(f"Nav error ({strategy}): {e}")
                    continue
            if attempt < retries - 1:
                wait_sec = 2 ** attempt + 1
                self.log.warn(f"Retry {attempt+1}/{retries} in {wait_sec}s…")
                time.sleep(wait_sec)

        self.log.error(f"Failed to navigate: {url[:70]}")
        return None

    def get_current_url(self) -> str:
        try:
            return self._page.url
        except Exception:
            return ""

    def screenshot(self, path: Path):
        try:
            self._page.screenshot(path=str(path), full_page=True)
        except Exception:
            pass

    @property
    def intercepted_api_data(self) -> Dict[str, Any]:
        return copy.deepcopy(self._intercepted)


# ─────────────────────────────────────────────────────────────────────────────
# AUTHENTICATION
# ─────────────────────────────────────────────────────────────────────────────

class EtLabAuth:
    """Multi-strategy login: CSS selectors → JS injection → Enter key."""

    LOGIN_PATTERNS = [
        ('input[name="LoginForm[username]"]', 'input[name="LoginForm[password]"]'),
        ('#LoginForm_username',               '#LoginForm_password'),
        ('input[name="username"]',            'input[name="password"]'),
        ('input[type="text"]',                'input[type="password"]'),
    ]
    SUBMIT_PATTERNS = [
        'input[type="submit"]',
        'button[type="submit"]',
        'button:has-text("Login")',
        '.btn-primary',
    ]

    def __init__(self, engine: PlaywrightEngine, log: EtLabLogger):
        self.engine    = engine
        self.log       = log
        self.logged_in = False

    def login(self, username: str, password: str, max_attempts: int = 3) -> bool:
        login_url = urljoin(BASE_URL, "/user/login")
        for attempt in range(1, max_attempts + 1):
            self.log.info(f"Login attempt {attempt}/{max_attempts}…")
            html = self.engine.navigate(login_url, wait="domcontentloaded")
            if not html:
                self.log.error("Could not load login page")
                continue

            self.engine.screenshot(OUTPUT_DIR / "debug_login.png")
            page = self.engine._page

            filled = False
            for user_sel, pass_sel in self.LOGIN_PATTERNS:
                try:
                    u_el = page.query_selector(user_sel)
                    p_el = page.query_selector(pass_sel)
                    if not (u_el and p_el):
                        continue
                    u_el.fill("")
                    u_el.type(username, delay=40)
                    p_el.fill("")
                    p_el.type(password, delay=40)
                    self.log.debug(f"Filled: {user_sel}")

                    clicked = False
                    for sub_sel in self.SUBMIT_PATTERNS:
                        btn = page.query_selector(sub_sel)
                        if btn:
                            btn.click()
                            clicked = True
                            break
                    if not clicked:
                        p_el.press("Enter")

                    try:
                        page.wait_for_load_state("networkidle", timeout=10000)
                    except Exception:
                        page.wait_for_timeout(3000)

                    cur = self.engine.get_current_url()
                    if "login" not in cur.lower():
                        self.log.success(f"Login OK → {cur}")
                        self.logged_in = True
                        return True

                    body_text = page.inner_text("body") or ""
                    if any(kw in body_text.lower() for kw in ["invalid", "incorrect", "wrong"]):
                        self.log.error("Wrong credentials.")
                        return False

                    filled = True
                    break
                except Exception as e:
                    self.log.debug(f"Pattern {user_sel} failed: {e}")
                    continue

            if not filled:
                # JS injection fallback
                self.log.warn("Trying JS injection login…")
                try:
                    page.evaluate(f"""() => {{
                        let u = document.querySelector('input[type="text"],input[type="email"]');
                        let p = document.querySelector('input[type="password"]');
                        if (u) u.value = '{username}';
                        if (p) p.value = '{password}';
                        let f = document.querySelector('form');
                        if (f) f.submit();
                    }}""")
                    page.wait_for_timeout(3000)
                    if "login" not in self.engine.get_current_url().lower():
                        self.log.success("JS login worked!")
                        self.logged_in = True
                        return True
                except Exception as e:
                    self.log.warn(f"JS injection failed: {e}")

            if attempt < max_attempts:
                time.sleep(3 * attempt)

        self.log.error("All login strategies exhausted.")
        return False


# ─────────────────────────────────────────────────────────────────────────────
# HTML PARSER
# ─────────────────────────────────────────────────────────────────────────────

class EtLabParser:
    """
    Handles all EtLab HTML parsing.

    Key fixes vs v3:
    ─────────────────
    parse_subject_summary():
        The attendance-subject page is a PIVOT TABLE:
          columns = [UNi Reg No, Roll No, Name, <code1>, <code2>, …, Total, Percentage]
          one data row per student
        Each subject-code cell contains "51/62 (82%)" → present/total(pct%).
        Non-subject columns are skipped via ATTENDANCE_TABLE_SKIP_COLS.

    parse_results():
        The results page has multiple widget-box sections each with its own
        <table>:  Sessional · Module Test · Assignments · Tutorials · Seminars
        Columns are: Subject | Semester | Exam | Maximum Marks | Marks Obtained
        Maximum Marks comes BEFORE Marks Obtained — they were reversed in v3.
        Empty / colspan rows ("No class projects yet") are silently skipped.

    discover_batch_id():
        Prefers long encoded IDs (>= 10 digits) from href patterns like
        /viewattendancesubject/32481378255 over short 3-4 digit IDs that
        could collide with the student DB ID.
    """

    def __init__(self, log: EtLabLogger):
        self.log           = log
        self._subject_trie = Trie()
        # code → full name mapping built from results page
        self._code_to_name: Dict[str, str] = {}

    # ── helpers ───────────────────────────────────────────────────────────

    @staticmethod
    def _soup(html: str) -> BeautifulSoup:
        for parser in ["lxml", "html.parser"]:
            try:
                return BeautifulSoup(html, parser)
            except Exception:
                continue
        return BeautifulSoup(html, "html.parser")

    @staticmethod
    def _clean(text: str) -> str:
        if not text:
            return ""
        text = re.sub(r'\s+', ' ', text).strip()
        text = text.replace('\xa0', ' ').replace('\u200b', '')
        return text

    @staticmethod
    def _extract_numbers(text: str) -> List[int]:
        return [int(m) for m in re.findall(r'\b(\d+)\b', text)]

    @staticmethod
    def _detect_cell_status(cell: Tag) -> AttendanceStatus:
        """Detect presence/absence from CSS classes, style, title, text."""
        if not cell:
            return AttendanceStatus.UNKNOWN
        classes = cell.get("class") or []
        status  = AttendanceStatus.from_classes(classes)
        if status != AttendanceStatus.UNKNOWN:
            return status
        style = cell.get("style", "").lower()
        if "green" in style:  return AttendanceStatus.PRESENT
        if "red"   in style:  return AttendanceStatus.ABSENT
        title = (cell.get("title") or cell.get("data-original-title") or "").lower()
        if "present" in title: return AttendanceStatus.PRESENT
        if "absent"  in title: return AttendanceStatus.ABSENT
        if "duty"    in title: return AttendanceStatus.DUTY_LEAVE
        if "medical" in title: return AttendanceStatus.MEDICAL
        text = cell.get_text(strip=True).upper()
        if text in ("P", "PRESENT"):  return AttendanceStatus.PRESENT
        if text in ("A", "ABSENT"):   return AttendanceStatus.ABSENT
        if text in ("DL", "DUTY"):    return AttendanceStatus.DUTY_LEAVE
        if text in ("ML", "MEDICAL"): return AttendanceStatus.MEDICAL
        return AttendanceStatus.UNKNOWN

    def _parse_subject_cell(self, cell: Tag) -> Tuple[str, str, str]:
        """Return (code, name, topic) from an attendance-date cell."""
        if not cell:
            return "", "", ""
        anchor = cell.find("a")
        el     = anchor if anchor else cell
        main   = ""
        for content in el.children:
            if isinstance(content, NavigableString) and content.strip():
                main = self._clean(str(content))
                break
        if not main:
            main = self._clean(el.get_text())
        span  = el.find("span")
        topic = self._clean(span.get_text()) if span else ""
        m = re.match(r"^([A-Z0-9]{6,})\s*[-–:]\s*(.+)$", main, re.IGNORECASE)
        if m:
            return m.group(1).strip(), m.group(2).strip(), topic
        return "", main, topic

    # ── attendance date page ──────────────────────────────────────────────

    def parse_attendance_page(self, html: str) -> Tuple[List[AttendanceRecord], str, str]:
        """
        Parse the date-wise attendance table.
        Each row is a date (<th>), each TD is a class period.
        Returns (records, month_pct, overall_pct).
        """
        soup        = self._soup(html)
        records     = []
        month_pct   = ""
        overall_pct = ""

        for el in soup.find_all(string=re.compile(r'\d+\.?\d*\s*%')):
            text = str(el)
            if "month" in text.lower():
                m = re.search(r'(\d+\.?\d*)%', text)
                if m:
                    month_pct = m.group(1) + "%"
            if any(w in text.lower() for w in ["overall", "till", "total"]):
                m = re.search(r'(\d+\.?\d*)%', text)
                if m:
                    overall_pct = m.group(1) + "%"

        for table in soup.find_all("table"):
            r = self._parse_date_table(table)
            records.extend(r)

        if not records:
            records = self._parse_div_layout(soup)

        self.log.debug(f"Parsed {len(records)} date-view attendance records")
        return records, month_pct, overall_pct

    def _parse_date_table(self, table: Tag) -> List[AttendanceRecord]:
        records = []
        for row in table.find_all("tr"):
            date_cell = row.find("th")
            if not date_cell:
                continue
            date_text = self._clean(date_cell.get_text())
            if not date_text or not re.search(r'\d', date_text):
                continue
            row_cls = " ".join(row.get("class") or []).lower()
            if any(k in row_cls for k in ["holiday", "sunday", "weekend"]):
                continue
            for idx, cell in enumerate(row.find_all("td"), start=1):
                status = self._detect_cell_status(cell)
                if status in (AttendanceStatus.UNKNOWN, AttendanceStatus.HOLIDAY):
                    continue
                code, name, topic = self._parse_subject_cell(cell)
                if not name and not code:
                    continue
                records.append(AttendanceRecord(
                    date=date_text, day_of_week="",
                    subject_code=code, subject_name=name,
                    status=status, period=idx, topic=topic,
                    raw_class=" ".join(cell.get("class") or []),
                ))
        return records

    def _parse_div_layout(self, soup: BeautifulSoup) -> List[AttendanceRecord]:
        records = []
        for card in soup.find_all("div", class_=re.compile(r"attend|card|item", re.I)):
            status = AttendanceStatus.from_classes(card.get("class") or [])
            if status == AttendanceStatus.UNKNOWN:
                continue
            date_el = card.find(class_=re.compile(r"date|day", re.I))
            subj_el = card.find(class_=re.compile(r"subject|course|name", re.I))
            name    = self._clean(subj_el.get_text()) if subj_el else ""
            if name:
                records.append(AttendanceRecord(
                    date=self._clean(date_el.get_text()) if date_el else "",
                    day_of_week="", subject_code="", subject_name=name,
                    status=status, period=0,
                ))
        return records

    # ── attendance subject summary page (PIVOT TABLE) ─────────────────────

    def parse_subject_summary(self, html: str) -> Dict[str, SubjectAttendance]:
        """
        The EtLab subject-attendance page is a PIVOT / wide-format table:

          | UNi Reg No | Roll No | Name | 25DSBST201 | 25DSBSP202 | … | Total | Percentage |
          | UKP25CD030 |   30    | KAIL | 51/62 (82%)|65/75 (87%) | … | 381/… |    83%     |

        Steps:
          1. Find the <table class="items table-striped …">
          2. Read header row → locate subject-code columns (skip meta cols)
          3. Parse the single student data row
          4. For each subject col: extract present/total from "51/62 (82%)"
          5. Also capture Roll No and Reg No into a side-dict for profile enrichment
        """
        soup     = self._soup(html)
        subjects: Dict[str, SubjectAttendance] = {}

        # Grab the main data table — prefer class="items"
        table = soup.find("table", class_=re.compile(r"\bitems\b"))
        if not table:
            table = soup.find("table")
        if not table:
            self.log.warn("No table found in attendance-subject page")
            return subjects

        thead = table.find("thead")
        tbody = table.find("tbody")
        if not thead or not tbody:
            self.log.warn("Attendance subject table missing thead/tbody")
            return subjects

        raw_headers = [self._clean(th.get_text()) for th in thead.find_all("th")]
        self.log.debug(f"Pivot headers ({len(raw_headers)}): {raw_headers}")

        # Identify subject-code columns — anything that looks like a KTU code
        # and is NOT in the skip-set
        subject_cols: List[Tuple[int, str]] = []  # (col_index, code)
        for i, h in enumerate(raw_headers):
            if h.lower() in ATTENDANCE_TABLE_SKIP_COLS:
                continue
            # KTU subject codes: 8-11 uppercase alphanum chars
            if re.match(r'^[A-Z0-9]{6,12}$', h.strip()):
                subject_cols.append((i, h.strip()))

        self.log.debug(f"Subject columns found: {[c for _, c in subject_cols]}")

        if not subject_cols:
            self.log.warn("No subject-code columns detected in pivot table")
            return subjects

        # Find Roll No and Reg No column indices for profile enrichment
        roll_col = next((i for i, h in enumerate(raw_headers)
                         if "roll" in h.lower()), -1)
        reg_col  = next((i for i, h in enumerate(raw_headers)
                         if "reg" in h.lower() or "uni" in h.lower()), -1)

        data_rows = tbody.find_all("tr")
        if not data_rows:
            self.log.warn("No data rows in attendance pivot table")
            return subjects

        # Use the first data row (this is a single-student view)
        row   = data_rows[0]
        cells = row.find_all("td")
        texts = [self._clean(c.get_text()) for c in cells]

        self.log.debug(f"Pivot data row cells ({len(texts)}): {texts[:5]}…")

        # Side-capture: store roll/reg for profile enrichment
        if roll_col >= 0 and roll_col < len(texts):
            self._last_roll = texts[roll_col]
        if reg_col >= 0 and reg_col < len(texts):
            self._last_reg = texts[reg_col]

        for col_idx, code in subject_cols:
            if col_idx >= len(texts):
                self.log.warn(f"Column index {col_idx} out of range for code {code}")
                continue

            cell_text = texts[col_idx].strip()  # e.g. "51/62 (82%)"

            # Parse "present/total (pct%)"
            m = re.match(r'(\d+)\s*/\s*(\d+)\s*\((\d+(?:\.\d+)?)%\)', cell_text)
            if not m:
                # Try bare "present/total" without percentage
                m2 = re.match(r'(\d+)\s*/\s*(\d+)', cell_text)
                if not m2:
                    self.log.debug(f"Cannot parse cell '{cell_text}' for {code}")
                    continue
                present_count = int(m2.group(1))
                total_count   = int(m2.group(2))
            else:
                present_count = int(m.group(1))
                total_count   = int(m.group(2))

            absent_count = total_count - present_count

            # Resolve full subject name if already known from results
            full_name = self._code_to_name.get(code, code)

            sa = SubjectAttendance(
                code=code,
                name=full_name,
                total_classes=total_count,
                present=present_count,
                absent=absent_count,
            )
            subjects[full_name] = sa
            self._subject_trie.insert(full_name)
            self._subject_trie.insert(code)   # also index by code

        self.log.success(
            f"Pivot parser: {len(subjects)} subjects "
            f"({sum(s.total_classes for s in subjects.values())} total classes)"
        )
        return subjects

    # ── results page (multiple widget-box sections) ───────────────────────

    def parse_results(self, html: str) -> List[SeriesExam]:
        """
        The EtLab results page has multiple <div class="widget-box"> sections:
          • Sessional exams    → <h5>Sessional exams</h5>
          • Module Test        → <h5>Module Test</h5>
          • Class Projects     → often empty
          • Assignments        → may say "NOT SUBMITTED"
          • Tutorials          → often empty
          • Seminars           → often empty

        Each section has a <table class="items table"> with columns:
          Subject | Semester | Exam | Maximum Marks | Marks Obtained | View Response

        Columns are parsed by HEADER NAME not position, so future reordering
        won't break anything.

        Empty colspan rows ("No class projects yet") are skipped automatically.
        """
        soup    = self._soup(html)
        results: List[SeriesExam] = []

        for widget in soup.find_all("div", class_="widget-box"):
            title_el = widget.find("h5")
            category = self._clean(title_el.get_text()) if title_el else "Unknown"

            table = widget.find("table", class_=re.compile(r"\bitems\b"))
            if not table:
                continue

            thead = table.find("thead")
            tbody = table.find("tbody")
            if not thead or not tbody:
                continue

            raw_headers = [self._clean(th.get_text()).lower()
                           for th in thead.find_all("th")]

            # Build column index map by header keyword
            def _col(keyword: str) -> int:
                for i, h in enumerate(raw_headers):
                    if keyword in h:
                        return i
                return -1

            col_subject  = _col("subject")
            col_semester = _col("semester")
            col_exam     = max(_col("exam"), _col("assignment"), _col("title"), _col("name"))
            col_max      = _col("maximum")
            col_obtained = _col("obtained")

            # col_exam: pick the first non-(-1) among those
            for kw in ["exam", "assignment", "title", "class project", "name"]:
                idx = _col(kw)
                if idx >= 0:
                    col_exam = idx
                    break

            for row in tbody.find_all("tr"):
                cells = row.find_all("td")

                # Skip empty / colspan placeholder rows
                if len(cells) == 1:
                    continue
                if not cells:
                    continue

                texts = [self._clean(c.get_text()) for c in cells]

                # Skip if all cells empty
                if not any(t for t in texts):
                    continue

                # Parse subject column: "CODE - FULL NAME"
                subject_text = texts[col_subject] if 0 <= col_subject < len(texts) else ""
                if not subject_text:
                    continue

                code = ""
                name = subject_text
                sm   = re.match(r'^([A-Z0-9]{6,})\s*[-–]\s*(.+)$', subject_text)
                if sm:
                    code = sm.group(1).strip()
                    name = sm.group(2).strip()
                    # Register in global code→name map for attendance enrichment
                    self._code_to_name[code] = name

                semester   = texts[col_semester] if 0 <= col_semester < len(texts) else ""
                exam_label = texts[col_exam]     if 0 <= col_exam     < len(texts) else ""
                max_marks  = texts[col_max]      if 0 <= col_max      < len(texts) else ""
                obtained   = texts[col_obtained] if 0 <= col_obtained < len(texts) else ""

                # Skip rows where subject is a placeholder message
                if re.match(r'^no\b', name.lower()):
                    continue

                results.append(SeriesExam(
                    category=category,
                    subject_code=code,
                    subject_name=name,
                    semester=semester,
                    exam_label=exam_label,
                    max_marks=max_marks,
                    marks_obtained=obtained,
                ))

        self.log.success(f"Results parser: {len(results)} entries across all sections")
        return results

    # ── profile ───────────────────────────────────────────────────────────

    def parse_profile(self, html: str) -> StudentProfile:
        """Multi-strategy profile parser: table → dl → headings → title."""
        soup    = self._soup(html)
        profile = StudentProfile()

        field_map = {
            "name": "name", "student name": "name",
            "roll":   "roll_number", "rollno": "roll_number",
            "register": "roll_number",
            "department": "department", "branch": "department", "dept": "department",
            "semester": "semester", "sem": "semester",
            "batch":   "batch",
            "email":   "email",
            "phone":   "phone", "mobile": "phone",
            "college": "college", "institution": "college",
        }

        for table in soup.find_all("table"):
            for row in table.find_all("tr"):
                cells = row.find_all(["td", "th"])
                if len(cells) < 2:
                    continue
                key = self._clean(cells[0].get_text()).lower()
                val = self._clean(cells[1].get_text())
                for k, attr in field_map.items():
                    if k in key and not getattr(profile, attr):
                        setattr(profile, attr, val)

        if not profile.name:
            for dl in soup.find_all("dl"):
                for dt, dd in zip(dl.find_all("dt"), dl.find_all("dd")):
                    if "name" in self._clean(dt.get_text()).lower():
                        profile.name = self._clean(dd.get_text())
                        break

        if not profile.name:
            # Try navbar username display
            for el in soup.find_all("span", class_="text"):
                t = self._clean(el.get_text())
                if t and 3 < len(t) < 60:
                    skip = {"dashboard", "profile", "etlab", "home", "login",
                            "logout", "messages", "inbox"}
                    if not any(w in t.lower() for w in skip):
                        profile.name = t
                        break

        # Pull name from page title as last resort
        if not profile.name:
            title_el = soup.find("title")
            if title_el:
                parts = re.split(r'[-|–—]', title_el.get_text())
                cand  = self._clean(parts[0]) if parts else ""
                if cand and "etlab" not in cand.lower():
                    profile.name = cand

        # College from header
        if not profile.college:
            header = soup.find(id="header") or soup.find(class_="dash-date")
            if header:
                t = self._clean(header.get_text())
                if "college" in t.lower() or "university" in t.lower():
                    profile.college = t

        return profile

    # ── timetable ─────────────────────────────────────────────────────────

    def parse_timetable(self, html: str) -> List[TimetableSlot]:
        soup  = self._soup(html)
        slots: List[TimetableSlot] = []
        DAYS  = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]

        for table in soup.find_all("table"):
            rows = table.find_all("tr")
            if len(rows) < 2:
                continue
            period_hdrs = [self._clean(c.get_text()) for c in rows[0].find_all(["th", "td"])]

            for r_idx, row in enumerate(rows[1:]):
                cells = row.find_all(["td", "th"])
                if not cells:
                    continue
                day_text = self._clean(cells[0].get_text())
                day      = next(
                    (d for d in DAYS if d.lower() in day_text.lower()),
                    DAYS[r_idx] if r_idx < len(DAYS) else f"Day {r_idx+1}",
                )
                for c_idx, cell in enumerate(cells[1:], start=1):
                    text = self._clean(cell.get_text())
                    if not text or text in ("-", "—"):
                        continue
                    m    = re.match(r"^([A-Z0-9]+)\s*[-:]\s*(.+)$", text)
                    code = m.group(1) if m else ""
                    name = m.group(2) if m else text
                    hdr  = period_hdrs[c_idx] if c_idx < len(period_hdrs) else ""
                    tm   = re.search(r"(\d+:\d+)\s*[-–]\s*(\d+:\d+)", hdr)
                    slots.append(TimetableSlot(
                        day=day, period=c_idx,
                        subject_code=code, subject_name=name,
                        start_time=tm.group(1) if tm else "",
                        end_time=tm.group(2)   if tm else "",
                    ))
        return slots

    # ── batch ID discovery ────────────────────────────────────────────────

    def discover_batch_id(self, html: str) -> Tuple[str, str, str]:
        """
        Returns (batch_id, batch_id_encoded, student_db_id).

        Priority: long encoded IDs (>= 10 digits) from known URL patterns
        are preferred to avoid collisions with the 4-digit student DB ID.
        """
        soup    = self._soup(html)
        batch_id = batch_id_enc = student_db_id = ""

        all_hrefs  = [a.get("href", "") for a in soup.find_all("a", href=True)]
        all_hrefs += [f.get("action", "") for f in soup.find_all("form", action=True)]
        all_text   = " ".join(s.get_text() for s in soup.find_all("script"))

        # Pattern priority: long encoded IDs first
        for source in all_hrefs:
            if not source:
                continue
            # Long encoded batch ID (>= 10 digits) from known URL patterns
            m = re.search(r'viewattendancesubject/(\d{8,})', source)
            if m and not batch_id_enc:
                batch_id_enc = m.group(1)
            m = re.search(r'viewsubjectattendancemonth/(\d{8,})', source)
            if m and not batch_id_enc:
                batch_id_enc = m.group(1)
            # Short numeric batch ID from form action
            m = re.search(r'viewattendancesubject/(\d{3,7})', source)
            if m and not batch_id:
                batch_id = m.group(1)
            # student_db_id from medical leave / student profile URL
            m = re.search(r'/medicalleave/(\d+)', source)
            if m and not student_db_id:
                student_db_id = m.group(1)
            m = re.search(r'student_id=(\d+)', source)
            if m and not student_db_id:
                student_db_id = m.group(1)

        # JS variables
        for pat, field in [
            (r'batchId\s*[=:]\s*["\']?(\d+)', 'batch_id'),
            (r'studentId\s*[=:]\s*["\']?(\d+)', 'student_db_id'),
        ]:
            m = re.search(pat, all_text)
            if m:
                val = m.group(1)
                if field == 'batch_id' and not batch_id:
                    batch_id = val
                elif field == 'student_db_id' and not student_db_id:
                    student_db_id = val

        # Use encoded as primary if available (it's the real one EtLab uses)
        return batch_id_enc or batch_id, batch_id_enc, student_db_id


# ─────────────────────────────────────────────────────────────────────────────
# SCRAPER ORCHESTRATOR
# ─────────────────────────────────────────────────────────────────────────────

class EtLabScraper:
    """
    Orchestrates the full scrape lifecycle:
      login → dashboard → profile → attendance → results → timetable → consolidate
    """

    def __init__(self, username: str, password: str, headless: bool = True,
                 no_cache: bool = False, semester: int = 0, log: EtLabLogger = None):
        self.username  = username
        self.password  = password
        self.semester  = semester
        self.log       = log or EtLabLogger()
        self.engine    = PlaywrightEngine(self.log, headless=headless)
        self.auth      = EtLabAuth(self.engine, self.log)
        self.parser    = EtLabParser(self.log)
        self.data      = AcademicData()
        self.data.profile.student_id = username
        self._batch_id     = ""
        self._batch_id_enc = ""
        self._student_db_id = ""
        if no_cache:
            CacheManager(CACHE_DIR).clear()

    def _url(self, path: str) -> str:
        return urljoin(BASE_URL, path)

    def _try_endpoints(self, key: str, **fmt) -> Optional[str]:
        for pattern in ENDPOINT_PATTERNS.get(key, []):
            try:
                path = pattern.format(
                    batch_id=self._batch_id,
                    batch_id_enc=self._batch_id_enc,
                    student_id=self._student_db_id,
                    **fmt,
                )
            except KeyError:
                continue
            url     = self._url(path)
            spinner = _spinner(f"Fetching {key}")
            html    = self.engine.navigate(url)
            spinner.set()
            if html and len(html) > 1000:
                cur = self.engine.get_current_url()
                if "login" in cur.lower():
                    self.log.warn("Session expired mid-fetch")
                    return None
                self.data.scraped_pages[key] = ScrapedPage(url=url, html=html)
                (OUTPUT_DIR / f"debug_{key}.html").write_text(
                    html, encoding="utf-8", errors="replace"
                )
                self.log.success(f"Got {key} ({len(html):,} bytes)")
                return html
        self.log.warn(f"All endpoints failed: {key}")
        return None

    def _update_ids(self, html: str):
        bid, benc, sid = self.parser.discover_batch_id(html)
        if bid and not self._batch_id:
            self._batch_id = bid
            self.log.info(f"batch_id → {bid}")
        if benc and not self._batch_id_enc:
            self._batch_id_enc = benc
            self.log.info(f"batch_id_enc → {benc}")
        if sid and not self._student_db_id:
            self._student_db_id = sid
            self.log.info(f"student_db_id → {sid}")
        self.data.profile.batch_id      = self._batch_id
        self.data.profile.student_db_id = self._student_db_id

    def _check_api_intercepts(self) -> bool:
        api_data = self.engine.intercepted_api_data
        if not api_data:
            return False
        self.data.api_data = api_data
        found = False
        for url, payload in api_data.items():
            self.log.info(f"Checking intercepted API: {url[:60]}")
            items = payload if isinstance(payload, list) else None
            if isinstance(payload, dict):
                for key in ["attendance", "data", "records", "list"]:
                    if key in payload and isinstance(payload[key], list):
                        items = payload[key]
                        break
            if items:
                records = self._parse_api_attendance(items)
                if records:
                    self.data.attendance_records.extend(records)
                    found = True
        if found:
            self.log.success(
                f"API intercept: {len(self.data.attendance_records)} records"
            )
        return found

    def _parse_api_attendance(self, items: List[dict]) -> List[AttendanceRecord]:
        records = []
        for item in items:
            if not isinstance(item, dict):
                continue
            sv = (item.get("status") or item.get("attendance_status") or
                  item.get("present") or item.get("type") or "")
            subject = (item.get("subject_name") or item.get("subject") or
                       item.get("course_name") or "")
            date    = (item.get("date") or item.get("attendance_date") or "")
            if not subject:
                continue
            ss = str(sv).lower()
            if "present" in ss or sv in (1, True):
                status = AttendanceStatus.PRESENT
            elif "absent"  in ss or sv in (0, False):
                status = AttendanceStatus.ABSENT
            elif "duty"    in ss:
                status = AttendanceStatus.DUTY_LEAVE
            elif "medical" in ss:
                status = AttendanceStatus.MEDICAL
            else:
                continue
            records.append(AttendanceRecord(
                date=str(date), day_of_week="",
                subject_code=item.get("subject_code", ""),
                subject_name=str(subject),
                status=status, period=item.get("period", 0),
                topic=item.get("topic", ""),
            ))
        return records

    def scrape_all(self) -> AcademicData:
        OUTPUT_DIR.mkdir(exist_ok=True)
        try:
            self.engine.start()
        except Exception as e:
            self.log.critical(f"Browser start failed: {e}")
            self.data.add_error(str(e))
            return self.data

        try:
            # LOGIN
            if not self.auth.login(self.username, self.password):
                self.data.add_error("Login failed")
                return self.data

            # RESULTS first — so code→name map is populated before attendance
            self.log.info("Scraping results…")
            res_html = self._try_endpoints("results")
            if res_html:
                self._update_ids(res_html)
                self.data.series_results = self.parser.parse_results(res_html)
                self.log.success(f"Results: {len(self.data.series_results)} entries")

            # DASHBOARD
            self.log.info("Scraping dashboard…")
            dash_html = self._try_endpoints("dashboard")
            if dash_html:
                self._update_ids(dash_html)

            # PROFILE
            self.log.info("Scraping profile…")
            prof_html = self._try_endpoints("profile")
            if prof_html:
                self._update_ids(prof_html)
                self.data.profile = self.parser.parse_profile(prof_html)
                self.data.profile.student_id    = self.username
                self.data.profile.batch_id      = self._batch_id
                self.data.profile.student_db_id = self._student_db_id
                # Enrich from pivot table side-captures
                if hasattr(self.parser, "_last_roll") and not self.data.profile.roll_number:
                    self.data.profile.roll_number = self.parser._last_roll
                if hasattr(self.parser, "_last_reg") and not self.data.profile.reg_number:
                    self.data.profile.reg_number = self.parser._last_reg
                self.log.success(f"Profile: {self.data.profile.display_name}")

            # ATTENDANCE DATE VIEW
            self.log.info("Scraping attendance (date view)…")
            att_html = self._try_endpoints("attendance_date")
            if att_html:
                self._update_ids(att_html)
                recs, mpct, opct = self.parser.parse_attendance_page(att_html)
                self.data.attendance_records.extend(recs)
                self.log.info(f"Date view: {len(recs)} records | Month: {mpct} | Overall: {opct}")

            # ATTENDANCE SUBJECT VIEW (pivot table)
            if self._batch_id:
                self.log.info("Scraping attendance (subject pivot)…")
                subj_html = self._try_endpoints("attendance_subject")
                if subj_html:
                    subj_data = self.parser.parse_subject_summary(subj_html)
                    self.data.subject_attendance.update(subj_data)
                    # Also capture roll/reg from pivot
                    if hasattr(self.parser, "_last_roll") and not self.data.profile.roll_number:
                        self.data.profile.roll_number = self.parser._last_roll
                    if hasattr(self.parser, "_last_reg") and not self.data.profile.reg_number:
                        self.data.profile.reg_number = self.parser._last_reg

                month_html = self._try_endpoints("attendance_month")
                if month_html:
                    mrecs, _, _ = self.parser.parse_attendance_page(month_html)
                    self.data.attendance_records.extend(mrecs)

            # API intercepts
            self._check_api_intercepts()

            # TIMETABLE
            self.log.info("Scraping timetable…")
            tt_html = self._try_endpoints("timetable")
            if tt_html:
                self.data.timetable = self.parser.parse_timetable(tt_html)
                self.log.success(f"Timetable: {len(self.data.timetable)} slots")

            # CONSOLIDATE
            self._consolidate_attendance()
            self._enrich_subject_names()

        except KeyboardInterrupt:
            self.log.warn("Interrupted.")
        except Exception as e:
            self.log.error(f"Unexpected: {e}")
            self.log.debug(traceback.format_exc())
            self.data.add_error(str(e))
        finally:
            self.engine.stop()

        return self.data

    def _consolidate_attendance(self):
        """
        Merge raw AttendanceRecord list into SubjectAttendance objects.
        Deduplicates (subject, date) — best-status wins (present > duty > medical > absent).
        Only runs if the pivot-table parse produced nothing (fallback path).
        """
        # If pivot table already gave us subject_attendance, don't double-count
        if self.data.subject_attendance:
            self.log.info("Subject attendance already populated from pivot table — skipping consolidation")
            return

        STATUS_PRIORITY = {
            AttendanceStatus.PRESENT:    4,
            AttendanceStatus.DUTY_LEAVE: 3,
            AttendanceStatus.MEDICAL:    2,
            AttendanceStatus.ABSENT:     1,
            AttendanceStatus.UNKNOWN:    0,
        }

        subject_day:    Dict[str, Dict[str, AttendanceStatus]] = defaultdict(dict)
        subject_codes:  Dict[str, str]                         = {}
        subject_topics: Dict[str, List[str]]                   = defaultdict(list)

        for rec in self.data.attendance_records:
            key = rec.subject_name or rec.subject_code
            if not key:
                continue
            subject_codes[key] = rec.subject_code
            curr = subject_day[key].get(rec.date)
            if STATUS_PRIORITY.get(rec.status, 0) > STATUS_PRIORITY.get(curr, 0):
                subject_day[key][rec.date] = rec.status
            if rec.topic and rec.topic not in subject_topics[key]:
                subject_topics[key].append(rec.topic)

        for subject_name, day_map in subject_day.items():
            sa = SubjectAttendance(
                code=subject_codes.get(subject_name, ""),
                name=subject_name,
                topics=subject_topics[subject_name],
            )
            ring = RingBuffer(30)
            for date_str in sorted(day_map.keys(), key=lambda d: re.sub(r'\D', '', d)):
                status = day_map[date_str]
                sa.total_classes += 1
                ring.append(status)
                if status == AttendanceStatus.PRESENT:
                    sa.present += 1
                    sa.dates_present.append(date_str)
                elif status == AttendanceStatus.ABSENT:
                    sa.absent += 1
                    sa.dates_absent.append(date_str)
                elif status == AttendanceStatus.DUTY_LEAVE:
                    sa.duty_leave += 1
                elif status == AttendanceStatus.MEDICAL:
                    sa.medical_leave += 1
            self.data.subject_attendance[subject_name] = sa

        total = sum(s.total_classes for s in self.data.subject_attendance.values())
        if self.data.subject_attendance:
            self.log.success(
                f"Consolidated (fallback): {len(self.data.subject_attendance)} subjects, "
                f"{total} classes"
            )
        else:
            self.log.warn("No attendance data parsed. Check debug_attendance_*.html files.")

    def _enrich_subject_names(self):
        """
        After parse_results() has built _code_to_name, replace code-keyed
        SubjectAttendance entries with full-name keys.
        """
        code_to_name = self.parser._code_to_name
        if not code_to_name:
            return

        new_map: Dict[str, SubjectAttendance] = {}
        for key, sa in self.data.subject_attendance.items():
            if sa.name in code_to_name.values():
                new_map[sa.name] = sa
            elif sa.code in code_to_name:
                sa.name = code_to_name[sa.code]
                new_map[sa.name] = sa
            elif key in code_to_name:
                sa.name = code_to_name[key]
                new_map[sa.name] = sa
            else:
                new_map[key] = sa

        self.data.subject_attendance = new_map
        self.log.debug(f"Name enrichment complete: {list(new_map.keys())}")


# ─────────────────────────────────────────────────────────────────────────────
# ANALYTICS ENGINE
# ─────────────────────────────────────────────────────────────────────────────

class EtLabAnalytics:
    """
    Analytics on top of AcademicData:
    • summary()         — overall stats dict
    • what_if()         — attendance prediction simulator
    • bunk_planner()    — greedy strategy for remaining classes
    • series_summary()  — per-subject exam marks breakdown
    • risk_ranking()    — subjects sorted by urgency
    """

    def __init__(self, data: AcademicData):
        self.data          = data
        self._risk_heap    = MinHeap()
        self._subject_trie = Trie()
        self._df_subjects: Optional[Any] = None
        self._df_records:  Optional[Any] = None
        self._build_structures()

    def _build_structures(self):
        for name, sa in self.data.subject_attendance.items():
            self._subject_trie.insert(name)
            if sa.code:
                self._subject_trie.insert(sa.code)
            self._risk_heap.push(sa.percentage, sa)
        if PANDAS_OK:
            self._df_subjects = self._build_subjects_df()
            self._df_records  = self._build_records_df()

    def _build_subjects_df(self):
        if not self.data.subject_attendance:
            return pd.DataFrame()
        rows = []
        for name, sa in self.data.subject_attendance.items():
            rows.append({
                "code": sa.code, "name": name,
                "short": self._short(name),
                "total": sa.total_classes,
                "present": sa.present, "absent": sa.absent,
                "duty": sa.duty_leave, "medical": sa.medical_leave,
                "pct": sa.percentage, "raw_pct": sa.raw_percentage,
                "safe": sa.is_safe, "danger": sa.is_danger,
                "can_bunk": sa.classes_can_bunk,
                "need_attend": sa.classes_to_attend,
                "shortage": sa.shortage,
                "vibe": sa.vibe_check,
            })
        return pd.DataFrame(rows).sort_values("pct")

    def _build_records_df(self):
        if not self.data.attendance_records:
            return pd.DataFrame()
        return pd.DataFrame([r.to_dict() for r in self.data.attendance_records])

    @staticmethod
    def _short(name: str, n: int = 24) -> str:
        words = name.split()
        s = " ".join(words[:3])
        return (s[:n] + "…") if len(s) > n else s

    def summary(self) -> Dict[str, Any]:
        subjects = list(self.data.subject_attendance.values())
        if not subjects:
            return {}

        total_present = sum(s.effective_present for s in subjects)
        total_classes = sum(s.total_classes for s in subjects)
        total_absent  = sum(s.absent for s in subjects)
        overall_pct   = round(total_present / total_classes * 100, 2) if total_classes else 0.0

        safe_subs  = [s for s in subjects if s.is_safe]
        risky_subs = [s for s in subjects if not s.is_safe]

        risk_sorted = self._risk_heap.to_sorted_list()
        worst = risk_sorted[0][1]  if risk_sorted else None
        best  = risk_sorted[-1][1] if risk_sorted else None

        return {
            "total_subjects":    len(subjects),
            "total_classes":     total_classes,
            "total_present":     total_present,
            "total_absent":      total_absent,
            "overall_pct":       overall_pct,
            "safe_count":        len(safe_subs),
            "risky_count":       len(risky_subs),
            "danger_count":      sum(1 for s in subjects if s.is_danger),
            "total_can_bunk":    sum(s.classes_can_bunk for s in safe_subs),
            "total_need_attend": sum(s.classes_to_attend for s in risky_subs),
            "worst_subject":     worst.name if worst else "N/A",
            "worst_pct":         worst.percentage if worst else 0,
            "best_subject":      best.name if best else "N/A",
            "best_pct":          best.percentage if best else 0,
            "overall_vibe":      self._overall_vibe(overall_pct),
        }

    @staticmethod
    def _overall_vibe(pct: float) -> str:
        if pct >= 90: return "absolute nerd mode 🏆"
        if pct >= 80: return "solid attendance, no stress ✨"
        if pct >= 75: return "technically safe, don't push it 😬"
        if pct >= 65: return "thin ice fr fr ⚠️"
        if pct >= 50: return "BSOD (bro seriously on destruction) 💀"
        return             "detention% speedrun world record 🚨"

    def what_if(self, subject_query: str, attend_n: int, total_n: int) -> Dict[str, Any]:
        """Predict attendance after attending attend_n / total_n future classes."""
        matches = self._subject_trie.fuzzy_find(subject_query)
        if not matches:
            return {"error": "Subject not found"}
        _, best = matches[0]
        sa = self.data.subject_attendance.get(best)
        if not sa:
            # Maybe it was keyed differently
            for name, s in self.data.subject_attendance.items():
                if s.code.upper() == subject_query.upper() or best in name:
                    sa = s
                    best = name
                    break
        if not sa:
            return {"error": f"No data for: {best}"}

        new_pct = sa.predict_after_n_classes(total_n, attend_n)
        return {
            "subject": best,
            "current_pct": sa.percentage,
            "new_pct": new_pct,
            "change": round(new_pct - sa.percentage, 2),
            "still_safe": new_pct >= SAFE_THRESHOLD,
            "message": (
                f"Attending {attend_n}/{total_n} → {new_pct}% "
                + ("✅ safe!" if new_pct >= SAFE_THRESHOLD else "❌ still at risk")
            ),
        }

    def bunk_planner(self, days_remaining: int, classes_per_day: int = 5) -> Dict[str, Any]:
        """Greedy bunk strategy: attend at-risk subjects, skip safe ones."""
        plan = {}
        for sa in sorted(
            self.data.subject_attendance.values(),
            key=lambda s: (-s.shortage, s.percentage),
        ):
            if sa.is_safe:
                plan[sa.name] = {
                    "status": "safe",
                    "can_skip": sa.classes_can_bunk,
                    "advice": f"safe — can skip up to {sa.classes_can_bunk} 🎉",
                }
            else:
                weeks = sa.weeks_until_safe()
                plan[sa.name] = {
                    "status": "at_risk",
                    "need_attend": sa.classes_to_attend,
                    "advice": f"attend next {sa.classes_to_attend} (~{weeks} weeks)",
                    "weeks_to_safe": weeks,
                }
        return {
            "days_remaining": days_remaining,
            "total_remaining_classes": days_remaining * classes_per_day,
            "plan": plan,
        }

    def risk_ranking(self) -> List[SubjectAttendance]:
        """Return subjects sorted by urgency (most at-risk first)."""
        return [item for _, item in self._risk_heap.to_sorted_list()]

    def series_summary(self) -> Dict[str, List[SeriesExam]]:
        """Group series exam results by subject name."""
        out: Dict[str, List[SeriesExam]] = defaultdict(list)
        for exam in self.data.series_results:
            key = exam.subject_name or exam.subject_code
            out[key].append(exam)
        return dict(out)

    @property
    def df_subjects(self):
        return self._df_subjects

    @property
    def df_records(self):
        return self._df_records


# ─────────────────────────────────────────────────────────────────────────────
# TERMINAL DISPLAY
# ─────────────────────────────────────────────────────────────────────────────

class EtLabDisplay:
    """Terminal dashboard — clean, color-coded, gen-Z friendly."""

    def __init__(self, data: AcademicData, analytics: EtLabAnalytics):
        self.data      = data
        self.analytics = analytics

    def show_all(self):
        self.show_banner()
        self.show_profile()
        self.show_attendance_table()
        self.show_summary()
        self.show_risk_advice()
        if self.data.series_results:
            self.show_series_results()
        if self.data.errors:
            self.show_errors()

    def show_banner(self):
        lines = [
            C.bold(C.magenta("  ╔══════════════════════════════════════════╗")),
            C.bold(C.magenta("  ║    ETLAB PRO  —  YOUR ATTENDANCE BESTIE  ║")),
            C.bold(C.magenta("  ║   'know before you yolo the bunk'  🎓    ║")),
            C.bold(C.magenta("  ╚══════════════════════════════════════════╝")),
            C.dim(f"  Scraped at: {self.data.scraped_at[:19]}"),
        ]
        print("\n" + "\n".join(lines) + "\n")

    def show_profile(self):
        p = self.data.profile
        lines = [
            f"  👤  {C.bold(p.display_name)}",
            f"  🏫  {p.college or 'UKF College of Engineering and Technology'}",
            f"  🎓  {p.department or 'N/A'}  |  Semester {p.semester or 'N/A'}",
            f"  🔑  ID: {p.student_id}  |  Roll: {p.roll_number or 'N/A'}"
            + (f"  |  Reg: {p.reg_number}" if p.reg_number else ""),
        ]
        print(_box(lines, title="STUDENT PROFILE", color=C.BCYAN))
        print()

    def show_attendance_table(self):
        subjects = self.data.subject_attendance
        if not subjects:
            print(C.yellow("  ⚠️  No attendance data. Check debug_attendance_subject.html"))
            return

        print(C.bold(C.cyan("\n  📊 SUBJECT-WISE ATTENDANCE\n")))

        headers = [
            "Subject", "Code", "Tot", "Pre", "Abs", "Dty", "%",
            "Progress", "Status", "Bunk💤", "Need📚",
        ]
        rows = []
        for sa in sorted(subjects.values(), key=lambda s: s.percentage):
            pct     = sa.percentage
            pct_str = (C.green if sa.is_safe else C.red)(f"{pct:.1f}%")
            bar     = _progress_bar(pct, width=10, show_pct=False)
            status  = (
                C.green("✅ SAFE") if sa.is_safe else
                (C.red("💀 DEAD") if sa.is_danger else C.yellow("⚠️  RISK"))
            )
            bunk = C.green(str(sa.classes_can_bunk)) if sa.is_safe else C.dim("-")
            need = C.red(str(sa.classes_to_attend))  if not sa.is_safe else C.dim("-")
            name_s = (sa.name[:25] + "…") if len(sa.name) > 25 else sa.name

            rows.append([
                name_s, sa.code or "-",
                str(sa.total_classes),
                str(sa.effective_present),
                str(sa.absent),
                str(sa.duty_leave),
                pct_str, bar, status, bunk, need,
            ])

        print(_table(headers, rows, max_col=27))
        print()

    def show_summary(self):
        s = self.analytics.summary()
        if not s:
            return

        pct       = s["overall_pct"]
        pct_color = C.green if pct >= 75 else C.red

        lines = [
            f"  🎯  Overall Attendance : {pct_color(f'{pct}%')}  {_progress_bar(pct, width=18)}",
            f"  📚  Total Classes       : {s['total_classes']}  "
            f"({C.green(str(s['total_present']) + ' present')} / "
            f"{C.red(str(s['total_absent']) + ' absent')})",
            f"  ✅  Safe    : {C.green(str(s['safe_count']))}  "
            f"⚠️  At Risk : {C.yellow(str(s['risky_count']))}  "
            f"💀 Danger  : {C.red(str(s['danger_count']))}",
            f"  💤  Bunk Budget         : {C.green(str(s['total_can_bunk']))} classes total",
            f"  📖  Need to Attend      : {C.red(str(s['total_need_attend']))} classes total",
            f"  🏆  Best   : {C.green(s['best_subject'][:38])} ({s['best_pct']}%)",
            f"  💀  Worst  : {C.red(s['worst_subject'][:38])} ({s['worst_pct']}%)",
            f"\n  🔥  Vibe   : {C.magenta(s['overall_vibe'])}",
        ]
        print(_box(lines, title="ACADEMIC SUMMARY", color=C.BMAGENTA))
        print()

    def show_risk_advice(self):
        """Per-subject advice sorted by urgency."""
        print(C.bold(C.cyan("  💬 Subject Status & Advice\n")))
        for sa in self.analytics.risk_ranking():
            emoji   = sa.status_emoji
            vibe    = sa.vibe_check
            weeks   = sa.weeks_until_safe()
            week_s  = f"  (~{weeks} weeks to safety)" if weeks and not sa.is_safe else ""
            print(
                f"  {emoji}  {C.bold(sa.name[:40])}\n"
                f"      {sa.code}  {_progress_bar(sa.percentage, width=14)}  "
                f"{C.dim(vibe)}{C.yellow(week_s)}"
            )
        print()

    def show_series_results(self):
        """
        Show series exam results per subject with per-exam and average marks.
        Grouped by category (Sessional, Module Test, Assignment…).
        """
        print(C.bold(C.cyan("\n  📝 SERIES EXAM RESULTS\n")))

        by_category: Dict[str, List[SeriesExam]] = defaultdict(list)
        for exam in self.data.series_results:
            by_category[exam.category].append(exam)

        for category, exams in by_category.items():
            print(C.bold(C.yellow(f"  ── {category} ─────────────────────────────────")))
            headers = ["Subject", "Code", "Exam", "Max", "Obtained", "%"]
            rows    = []
            for e in exams:
                pct_s = f"{e.percentage}%" if e.percentage is not None else "-"
                if e.percentage is not None:
                    pct_colored = (C.green if e.percentage >= 50 else C.red)(pct_s)
                else:
                    pct_colored = C.dim(pct_s)
                ob_colored = (
                    C.dim(e.marks_obtained) if not e.is_submitted
                    else e.marks_obtained
                )
                rows.append([
                    (e.subject_name[:30] + "…") if len(e.subject_name) > 30 else e.subject_name,
                    e.subject_code,
                    e.exam_label,
                    e.max_marks,
                    ob_colored,
                    pct_colored,
                ])
            print(_table(headers, rows, max_col=32))
            print()

    def show_errors(self):
        if not self.data.errors:
            return
        print(C.yellow("\n  ⚠️  Scraping errors:"))
        for err in self.data.errors:
            print(C.dim(f"    {err}"))
        print()

    def show_ascii_calendar(self, subject_name: str):
        """Print a simple ASCII attendance calendar for one subject."""
        sa = self.data.subject_attendance.get(subject_name)
        if not sa:
            # fuzzy fallback
            matches = Trie()
            for n in self.data.subject_attendance:
                matches.insert(n)
            found = matches.fuzzy_find(subject_name)
            if not found:
                print(C.red("  Subject not found"))
                return
            subject_name = found[0][1]
            sa = self.data.subject_attendance[subject_name]

        all_dates = set(sa.dates_present + sa.dates_absent)
        if not all_dates:
            print(C.dim("  No date data available for calendar view"))
            return

        # Parse dates (try DD-MM-YYYY, DD/MM/YYYY, etc.)
        parsed: Dict[datetime, str] = {}
        for ds in all_dates:
            for fmt in ("%d-%m-%Y", "%d/%m/%Y", "%Y-%m-%d", "%d %b %Y"):
                try:
                    dt = datetime.strptime(ds.strip(), fmt)
                    parsed[dt] = "P" if ds in sa.dates_present else "A"
                    break
                except ValueError:
                    continue

        if not parsed:
            print(C.dim("  Could not parse dates for calendar"))
            return

        min_dt = min(parsed)
        max_dt = max(parsed)
        print(C.bold(C.cyan(f"\n  📅 Attendance Calendar: {subject_name[:50]}\n")))

        cur_month = min_dt.replace(day=1)
        while cur_month <= max_dt:
            y, mo = cur_month.year, cur_month.month
            print(C.bold(f"  {cal_module.month_name[mo]} {y}"))
            print(C.dim("  Mo Tu We Th Fr Sa Su"))
            week = cal_module.monthcalendar(y, mo)
            for w in week:
                row_parts = []
                for d in w:
                    if d == 0:
                        row_parts.append("  ")
                    else:
                        dt = datetime(y, mo, d)
                        status = parsed.get(dt)
                        if status == "P":
                            row_parts.append(C.green(f"{d:2d}"))
                        elif status == "A":
                            row_parts.append(C.red(f"{d:2d}"))
                        else:
                            row_parts.append(C.dim(f"{d:2d}"))
                print("  " + " ".join(row_parts))
            print()
            # advance month
            if mo == 12:
                cur_month = cur_month.replace(year=y + 1, month=1)
            else:
                cur_month = cur_month.replace(month=mo + 1)

    def interactive_what_if(self):
        subjects = list(self.data.subject_attendance.keys())
        if not subjects:
            return
        print(C.bold(C.cyan("\n  🔮 WHAT-IF SIMULATOR\n")))
        print("  Subjects (type name, code, or number):")
        for i, name in enumerate(subjects, 1):
            sa = self.data.subject_attendance[name]
            print(f"  {C.dim(str(i)+'.')} {name[:45]}  {C.dim(sa.code)}  "
                  f"{_progress_bar(sa.percentage, width=8)}")
        try:
            choice = input(C.cyan("\n  Subject > ")).strip()
            # Allow numeric selection
            try:
                idx = int(choice) - 1
                if 0 <= idx < len(subjects):
                    choice = subjects[idx]
            except ValueError:
                pass
            attend = int(input(C.cyan("  Classes you will attend > ")).strip())
            total  = int(input(C.cyan("  Out of how many total    > ")).strip())
            result = self.analytics.what_if(choice, attend, total)
            if "error" in result:
                print(C.red(f"  {result['error']}"))
            else:
                chg = result["change"]
                chg_str = C.green(f"+{chg}%") if chg >= 0 else C.red(f"{chg}%")
                print(_box([
                    f"  Subject : {C.bold(result['subject'][:45])}",
                    f"  Current : {C.cyan(str(result['current_pct']) + '%')}",
                    f"  After   : {C.green(str(result['new_pct']) + '%')}  ({chg_str})",
                    f"  {result['message']}",
                ], title="WHAT-IF RESULT", color=C.BBLUE))
        except (ValueError, KeyboardInterrupt):
            print(C.dim("  Skipped."))


# ─────────────────────────────────────────────────────────────────────────────
# VISUALIZER
# ─────────────────────────────────────────────────────────────────────────────

class EtLabVisualizer:
    """Dark-theme Matplotlib chart suite."""

    PALETTE = {
        "safe":    "#00e676",
        "danger":  "#ff1744",
        "warning": "#ffab40",
        "bg":      "#0d1117",
        "surface": "#161b22",
        "text":    "#e6edf3",
        "grid":    "#21262d",
        "accent":  "#58a6ff",
    }

    def __init__(self, analytics: EtLabAnalytics):
        self.analytics = analytics
        self.data      = analytics.data
        if MATPLOTLIB_OK:
            self._apply_theme()

    def _apply_theme(self):
        p = self.PALETTE
        plt.style.use("dark_background")
        plt.rcParams.update({
            "figure.facecolor": p["bg"],
            "axes.facecolor":   p["surface"],
            "axes.edgecolor":   p["grid"],
            "axes.labelcolor":  p["text"],
            "xtick.color":      p["text"],
            "ytick.color":      p["text"],
            "text.color":       p["text"],
            "grid.color":       p["grid"],
            "grid.alpha":       0.4,
            "font.family":      "monospace",
        })

    def _bar_color(self, pct: float) -> str:
        if pct >= 75:  return self.PALETTE["safe"]
        if pct >= 60:  return self.PALETTE["warning"]
        return self.PALETTE["danger"]

    def plot_all(self):
        if not MATPLOTLIB_OK:
            print(C.yellow("  matplotlib not available — skipping charts"))
            return
        if not self.data.subject_attendance:
            return
        print(C.dim("  Generating charts…"))
        try:
            self._plot_dashboard()
            self._plot_bunk_budget()
            self._plot_series_marks()
            self._plot_trend()
            print(C.green(f"  Charts saved → {OUTPUT_DIR}/"))
        except Exception as e:
            print(C.yellow(f"  Chart error: {e}"))
            if __debug__:
                traceback.print_exc()

    def _plot_dashboard(self):
        df = self.analytics.df_subjects
        if df is None or df.empty:
            return

        fig = plt.figure(figsize=(18, 10), facecolor=self.PALETTE["bg"])
        gs  = gridspec.GridSpec(2, 3, figure=fig, hspace=0.42, wspace=0.35)

        # ── horizontal bar chart ─────────────────────────────────────────
        ax1    = fig.add_subplot(gs[0, :2])
        colors = [self._bar_color(p) for p in df["pct"]]
        bars   = ax1.barh(df["short"], df["pct"], color=colors, height=0.62,
                          edgecolor=self.PALETTE["grid"], linewidth=0.4)
        ax1.axvline(75, color=self.PALETTE["warning"], ls="--", lw=1.5,
                    label="75% threshold", alpha=0.8)
        ax1.axvline(60, color=self.PALETTE["danger"],  ls=":",  lw=1.0,
                    label="60% danger",    alpha=0.6)
        for bar, pct in zip(bars, df["pct"]):
            ax1.text(min(bar.get_width() + 1, 108),
                     bar.get_y() + bar.get_height() / 2,
                     f"{pct:.1f}%", va="center", ha="left",
                     fontsize=8, color=self.PALETTE["text"], fontweight="bold")
        ax1.set_xlim(0, 113)
        ax1.set_xlabel("Attendance %")
        ax1.set_title("Subject-wise Attendance", fontsize=13, fontweight="bold",
                      color=self.PALETTE["text"], pad=10)
        ax1.legend(fontsize=8, framealpha=0.3)

        # ── pie chart ────────────────────────────────────────────────────
        ax2  = fig.add_subplot(gs[0, 2])
        subs = list(self.data.subject_attendance.values())
        tp   = sum(s.effective_present for s in subs)
        ta   = sum(s.absent            for s in subs)
        td   = sum(s.duty_leave        for s in subs)
        vals = [v for v in [tp, ta, td] if v > 0]
        lbls = [l for v, l in zip([tp, ta, td], ["Present", "Absent", "Duty"]) if v > 0]
        cols = [self.PALETTE[c] for c, v in
                zip(["safe", "danger", "warning"], [tp, ta, td]) if v > 0]
        if vals:
            _, _, auts = ax2.pie(
                vals, labels=lbls, colors=cols, autopct="%1.0f%%",
                startangle=90,
                wedgeprops={"edgecolor": self.PALETTE["bg"], "linewidth": 2},
                textprops={"color": self.PALETTE["text"], "fontsize": 8},
            )
            for at in auts:
                at.set_color(self.PALETTE["bg"])
                at.set_fontweight("bold")
        tot = sum(vals) or 1
        ax2.set_title(f"Overall: {round(tp/tot*100,1)}%", fontsize=12,
                      fontweight="bold", color=self.PALETTE["text"])

        # ── stacked bar ──────────────────────────────────────────────────
        ax3 = fig.add_subplot(gs[1, :2])
        x   = range(len(df))
        ax3.bar(x, df["present"], label="Present",
                color=self.PALETTE["safe"],    edgecolor=self.PALETTE["bg"], lw=0.4)
        ax3.bar(x, df["absent"], bottom=df["present"], label="Absent",
                color=self.PALETTE["danger"],  edgecolor=self.PALETTE["bg"], lw=0.4)
        ax3.bar(x, df["duty"],  bottom=df["present"] + df["absent"], label="Duty",
                color=self.PALETTE["warning"], edgecolor=self.PALETTE["bg"], lw=0.4)
        ax3.set_xticks(list(x))
        ax3.set_xticklabels(df["short"], rotation=30, ha="right", fontsize=8)
        ax3.set_ylabel("Classes")
        ax3.set_title("Present / Absent / Duty", fontsize=11, fontweight="bold",
                      color=self.PALETTE["text"])
        ax3.legend(fontsize=8, framealpha=0.3)

        # ── stats box ────────────────────────────────────────────────────
        ax4 = fig.add_subplot(gs[1, 2])
        ax4.axis("off")
        s   = self.analytics.summary()
        txt = (
            f"BUNK BUDGET 💤\n\n"
            f"  {s.get('total_can_bunk',0):>5} classes\n\n"
            f"GRIND NEEDED 📚\n\n"
            f"  {s.get('total_need_attend',0):>5} classes\n\n"
            f"Safe:    {s.get('safe_count',0)}\n"
            f"At risk: {s.get('risky_count',0)}\n"
            f"Danger:  {s.get('danger_count',0)}"
        )
        ax4.text(0.05, 0.95, txt, transform=ax4.transAxes, va="top", ha="left",
                 fontsize=10, fontfamily="monospace", color=self.PALETTE["text"],
                 bbox=dict(boxstyle="round,pad=0.5", fc=self.PALETTE["surface"],
                           ec=self.PALETTE["accent"], lw=1.5))

        plt.suptitle(
            f"📊 {self.data.profile.display_name} — Attendance Report",
            fontsize=14, fontweight="bold", color=self.PALETTE["text"], y=1.01,
        )
        path = OUTPUT_DIR / "attendance_dashboard.png"
        plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
        plt.close()
        print(C.dim(f"    → {path}"))

    def _plot_bunk_budget(self):
        df = self.analytics.df_subjects
        if df is None or df.empty:
            return
        fig, ax = plt.subplots(figsize=(14, 5), facecolor=self.PALETTE["bg"])
        ax.set_facecolor(self.PALETTE["surface"])
        colors = [self.PALETTE["safe"] if v > 0 else self.PALETTE["danger"]
                  for v in df["can_bunk"]]
        ax.bar(df["short"], df["can_bunk"], color=colors,
               edgecolor=self.PALETTE["bg"], lw=0.4)
        ax.axhline(0, color=self.PALETTE["text"], lw=0.8)
        for i, (val, sho) in enumerate(zip(df["can_bunk"], df["shortage"])):
            if val == 0 and sho > 0:
                ax.text(i, -0.4, f"−{sho}", ha="center", va="top",
                        fontsize=8, color=self.PALETTE["danger"], fontweight="bold")
        ax.set_title("Bunk Budget (green = can skip  |  red = already short)",
                     fontsize=12, fontweight="bold", color=self.PALETTE["text"])
        ax.set_ylabel("Classes")
        plt.xticks(rotation=30, ha="right", fontsize=8)
        plt.tight_layout()
        path = OUTPUT_DIR / "bunk_budget.png"
        plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
        plt.close()
        print(C.dim(f"    → {path}"))

    def _plot_series_marks(self):
        """Bar chart of series exam marks per subject."""
        if not self.data.series_results:
            return
        # Only sessional exams with numeric marks
        sessionals = [
            e for e in self.data.series_results
            if "sessional" in e.category.lower() and e.percentage is not None
        ]
        if not sessionals:
            return

        subjects  = list(dict.fromkeys(e.subject_name for e in sessionals))
        exam_nums = sorted(set(e.exam_label for e in sessionals))
        x         = range(len(subjects))
        width     = 0.35
        colors    = [self.PALETTE["accent"], self.PALETTE["warning"]]

        fig, ax = plt.subplots(figsize=(14, 5), facecolor=self.PALETTE["bg"])
        ax.set_facecolor(self.PALETTE["surface"])

        for ei, enu in enumerate(exam_nums[:2]):   # max 2 exams per subject
            vals = []
            for subj in subjects:
                match = next(
                    (e for e in sessionals
                     if e.subject_name == subj and e.exam_label == enu),
                    None,
                )
                vals.append(match.percentage if match else 0)
            offset = (ei - 0.5) * width
            bars   = ax.bar(
                [xi + offset for xi in x], vals,
                width=width, label=f"Series {enu}",
                color=colors[ei % len(colors)],
                edgecolor=self.PALETTE["bg"], lw=0.4,
            )
            for bar, v in zip(bars, vals):
                if v > 0:
                    ax.text(
                        bar.get_x() + bar.get_width() / 2,
                        bar.get_height() + 1,
                        f"{v:.0f}%", ha="center", fontsize=7,
                        color=self.PALETTE["text"],
                    )

        ax.axhline(50, color=self.PALETTE["danger"], ls="--", lw=1.2,
                   label="50% pass line", alpha=0.7)
        ax.set_xticks(list(x))
        ax.set_xticklabels(
            [(s[:18] + "…") if len(s) > 18 else s for s in subjects],
            rotation=25, ha="right", fontsize=8,
        )
        ax.set_ylabel("Score %")
        ax.set_ylim(0, 110)
        ax.set_title("Series Exam Scores", fontsize=12, fontweight="bold",
                     color=self.PALETTE["text"])
        ax.legend(fontsize=8, framealpha=0.3)
        plt.tight_layout()
        path = OUTPUT_DIR / "series_marks.png"
        plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
        plt.close()
        print(C.dim(f"    → {path}"))

    def _plot_trend(self):
        """Attendance trend line from date-view records."""
        if not PANDAS_OK:
            return
        df = self.analytics.df_records
        if df is None or df.empty or "date" not in df.columns:
            return
        try:
            df = df.copy()
            df["date_parsed"] = pd.to_datetime(df["date"], dayfirst=True, errors="coerce")
            df = df.dropna(subset=["date_parsed"])
            if df.empty or len(df["date_parsed"].unique()) < 3:
                return

            daily = (
                df.groupby("date_parsed")
                .apply(lambda g: (g["status"] == AttendanceStatus.PRESENT.value).mean() * 100)
                .reset_index()
            )
            daily.columns = ["date", "pct"]
            daily = daily.sort_values("date")

            fig, ax = plt.subplots(figsize=(14, 4), facecolor=self.PALETTE["bg"])
            ax.set_facecolor(self.PALETTE["surface"])
            ax.fill_between(daily["date"], daily["pct"], alpha=0.25,
                            color=self.PALETTE["accent"])
            ax.plot(daily["date"], daily["pct"], color=self.PALETTE["accent"],
                    lw=2, marker="o", ms=3)
            ax.axhline(75, color=self.PALETTE["warning"], ls="--", lw=1.5,
                       label="75% threshold")

            if SCIPY_OK and len(daily) > 5:
                x_num = (daily["date"] - daily["date"].min()).dt.days.values
                slope, intercept, *_ = scipy_stats.linregress(x_num, daily["pct"].values)
                ax.plot(daily["date"], slope * x_num + intercept,
                        color=self.PALETTE["danger"], ls=":", lw=1.5,
                        label=f"Trend ({slope:+.2f}%/day)")

            ax.set_title("Daily Attendance Trend", fontsize=12, fontweight="bold",
                         color=self.PALETTE["text"])
            ax.set_ylabel("Attendance %")
            ax.legend(fontsize=8, framealpha=0.3)
            plt.xticks(rotation=30, ha="right", fontsize=8)
            plt.tight_layout()
            path = OUTPUT_DIR / "attendance_trend.png"
            plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
            plt.close()
            print(C.dim(f"    → {path}"))
        except Exception:
            pass  # trend is optional


# ─────────────────────────────────────────────────────────────────────────────
# EXPORTER
# ─────────────────────────────────────────────────────────────────────────────

class EtLabExporter:
    """Export to JSON, CSV, and Markdown."""

    def __init__(self, data: AcademicData, analytics: EtLabAnalytics):
        self.data      = data
        self.analytics = analytics

    def export_all(self):
        self._export_json()
        self._export_csv()
        self._export_markdown()

    def _export_json(self):
        path    = OUTPUT_DIR / "academic_data.json"
        payload = {
            "scraped_at": self.data.scraped_at,
            "profile":    asdict(self.data.profile),
            "summary":    self.analytics.summary(),
            "subjects":   {n: sa.to_dict() for n, sa in self.data.subject_attendance.items()},
            "series_results": [asdict(r) for r in self.data.series_results],
            "timetable":  [asdict(t) for t in self.data.timetable],
            "errors":     self.data.errors,
        }
        path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
        print(C.green(f"  📁 JSON : {path}"))

    def _export_csv(self):
        if PANDAS_OK:
            df = self.analytics.df_subjects
            if df is not None and not df.empty:
                p = OUTPUT_DIR / "attendance_summary.csv"
                df.to_csv(p, index=False)
                print(C.green(f"  📁 CSV  : {p}"))

            dr = self.analytics.df_records
            if dr is not None and not dr.empty:
                p2 = OUTPUT_DIR / "attendance_records.csv"
                dr.to_csv(p2, index=False)
                print(C.green(f"  📁 CSV  : {p2}"))

        # Series results CSV (always)
        if self.data.series_results:
            p3 = OUTPUT_DIR / "series_results.csv"
            lines = ["Category,Subject Code,Subject Name,Semester,Exam,Max Marks,Obtained,%"]
            for e in self.data.series_results:
                pct = str(e.percentage) if e.percentage is not None else ""
                lines.append(
                    f"{e.category},{e.subject_code},{e.subject_name},"
                    f"{e.semester},{e.exam_label},{e.max_marks},{e.marks_obtained},{pct}"
                )
            p3.write_text("\n".join(lines), encoding="utf-8")
            print(C.green(f"  📁 CSV  : {p3}"))

    def _export_markdown(self):
        path = OUTPUT_DIR / "attendance_report.md"
        s    = self.analytics.summary()
        p    = self.data.profile

        lines = [
            f"# 🎓 Attendance Report — {p.display_name}",
            f"**Generated:** {self.data.scraped_at[:19]}",
            f"**College:** {p.college}  |  **Department:** {p.department}  |  "
            f"**Semester:** {p.semester}",
            "",
            "## 📊 Overall Summary",
            "| Metric | Value |",
            "|--------|-------|",
            f"| Overall Attendance | **{s.get('overall_pct', 0)}%** |",
            f"| Total Classes | {s.get('total_classes', 0)} |",
            f"| Present | {s.get('total_present', 0)} |",
            f"| Absent | {s.get('total_absent', 0)} |",
            f"| Safe Subjects | {s.get('safe_count', 0)} |",
            f"| At Risk | {s.get('risky_count', 0)} |",
            f"| Bunk Budget | **{s.get('total_can_bunk', 0)} classes** |",
            f"| Need to Attend | **{s.get('total_need_attend', 0)} classes** |",
            "",
            "## 📋 Subject-wise Attendance",
            "| Subject | Code | Present | Total | % | Status | Bunk Left | Need |",
            "|---------|------|---------|-------|---|--------|-----------|------|",
        ]

        for name, sa in sorted(
            self.data.subject_attendance.items(),
            key=lambda x: x[1].percentage,
        ):
            status = "✅ Safe" if sa.is_safe else ("💀 Danger" if sa.is_danger else "⚠️ Risk")
            bunk   = str(sa.classes_can_bunk)  if sa.is_safe     else "-"
            need   = str(sa.classes_to_attend) if not sa.is_safe else "-"
            lines.append(
                f"| {name[:40]} | {sa.code} | {sa.effective_present} | "
                f"{sa.total_classes} | {sa.percentage}% | {status} | {bunk} | {need} |"
            )

        if self.data.series_results:
            lines += [
                "",
                "## 📝 Series Exam Results",
                "| Category | Subject | Exam | Max | Obtained | % |",
                "|----------|---------|------|-----|----------|---|",
            ]
            for e in self.data.series_results:
                pct = f"{e.percentage}%" if e.percentage is not None else "-"
                lines.append(
                    f"| {e.category} | {e.subject_name[:35]} | {e.exam_label} | "
                    f"{e.max_marks} | {e.marks_obtained} | {pct} |"
                )

        lines += ["", "---", "*Generated by EtLab Pro v4.0 — your attendance bestie 🎓*"]
        path.write_text("\n".join(lines), encoding="utf-8")
        print(C.green(f"  📁 MD   : {path}"))


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="EtLab Pro v4.0 — Your Attendance Bestie 🎓",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""
        Examples:
          python main1.py -u 925059 -p 6a014a
          python main1.py -u 925059 -p 6a014a --show-browser --debug
          python main1.py -u 925059 -p 6a014a --no-cache --no-charts
          python main1.py -u 925059 -p 6a014a --what-if
          python main1.py -u 925059 -p 6a014a --calendar "MATHEMATICS"
          python main1.py -u 925059 -p 6a014a --semester 2
        """),
    )
    p.add_argument("-u", "--username",   required=True,       help="EtLab student ID")
    p.add_argument("-p", "--password",   required=True,       help="EtLab password")
    p.add_argument("--show-browser",     action="store_true", help="Show browser window")
    p.add_argument("--no-cache",         action="store_true", help="Clear cache before run")
    p.add_argument("--no-charts",        action="store_true", help="Skip chart generation")
    p.add_argument("--no-export",        action="store_true", help="Skip file exports")
    p.add_argument("--what-if",          action="store_true", help="Interactive what-if simulator")
    p.add_argument("--calendar",         metavar="SUBJECT",   help="Show ASCII attendance calendar")
    p.add_argument("--debug",            action="store_true", help="Verbose debug logging")
    p.add_argument("--semester",         type=int, default=0, help="Semester number (0 = auto)")
    p.add_argument("-o", "--output",     default="etlab_output", help="Output directory")
    return p.parse_args()


def main():
    args = parse_args()

    global OUTPUT_DIR, CACHE_DIR, LOG_FILE
    OUTPUT_DIR = Path(args.output)
    CACHE_DIR  = OUTPUT_DIR / ".cache"
    LOG_FILE   = OUTPUT_DIR / "etlab.log"
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    log = EtLabLogger(
        level="DEBUG" if args.debug else "INFO",
        log_file=LOG_FILE,
    )

    if not PLAYWRIGHT_OK:
        log.critical("Playwright required: pip install playwright && playwright install chromium")
        sys.exit(1)
    if not BS4_OK:
        log.critical("beautifulsoup4 required: pip install beautifulsoup4 lxml")
        sys.exit(1)

    # ── SCRAPE ────────────────────────────────────────────────────────────
    scraper = EtLabScraper(
        username=args.username,
        password=args.password,
        headless=not args.show_browser,
        no_cache=args.no_cache,
        semester=args.semester,
        log=log,
    )
    data = scraper.scrape_all()

    # ── ANALYTICS ─────────────────────────────────────────────────────────
    analytics = EtLabAnalytics(data)

    # ── DISPLAY ───────────────────────────────────────────────────────────
    display = EtLabDisplay(data, analytics)
    display.show_all()

    # ── OPTIONAL ASCII CALENDAR ───────────────────────────────────────────
    if args.calendar and data.subject_attendance:
        display.show_ascii_calendar(args.calendar)

    # ── OPTIONAL WHAT-IF ──────────────────────────────────────────────────
    if args.what_if and data.subject_attendance:
        display.interactive_what_if()

    # ── CHARTS ────────────────────────────────────────────────────────────
    if not args.no_charts:
        viz = EtLabVisualizer(analytics)
        viz.plot_all()

    # ── EXPORT ────────────────────────────────────────────────────────────
    if not args.no_export:
        print(C.bold(C.cyan("\n  📦 Exporting…\n")))
        EtLabExporter(data, analytics).export_all()

    # ── FINAL VERDICT ─────────────────────────────────────────────────────
    s = analytics.summary()
    if s:
        pct = s["overall_pct"]
        if pct >= 75:
            print(C.green(f"\n  ✨ Overall {pct}% — you're doing great! Keep it up."))
        elif pct >= 60:
            print(C.yellow(f"\n  ⚠️  Overall {pct}% — borderline. Attend more consistently."))
        else:
            print(C.red(f"\n  💀 Overall {pct}% — seriously bro, start attending."))
    else:
        print(C.yellow("\n  ⚠️  No attendance data found."))
        print(C.dim("  Open etlab_output/debug_attendance_subject.html in a browser"))
        print(C.dim("  to inspect what the server returned."))

    print(C.dim(f"\n  Log    : {LOG_FILE}"))
    print(C.dim(f"  Output : {OUTPUT_DIR}/\n"))


if __name__ == "__main__":
    main()
