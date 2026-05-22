"""
╔══════════════════════════════════════════════════════════════════════════════╗
║   ETLAB PRO — YOUR ATTENDANCE BESTIE 🎓                                     ║
║   v3.0 | Playwright-powered | Bulletproof | Teen-friendly analytics         ║
║   "know before you yolo the bunk" — the only attendance tool you need       ║
╚══════════════════════════════════════════════════════════════════════════════╝

HOW IT WORKS:
  1. Playwright launches a real browser (invisible) — no bot detection issues
  2. Logs into EtLab using YOUR credentials
  3. Intercepts all network requests to find hidden JSON APIs
  4. Falls back to full HTML scraping if no APIs found
  5. Runs analytics: bunk budget, detention risk, what-if simulator
  6. Outputs color terminal dashboard + JSON + CSV + PNG charts

INSTALL:
  pip install playwright beautifulsoup4 pandas numpy matplotlib seaborn
  playwright install chromium
"""

# ─────────────────────────────────────────────────────────────────────────────
# IMPORTS — grouped by purpose
# ─────────────────────────────────────────────────────────────────────────────

# stdlib
import os
import re
import sys
import json
import time
import math
import heapq
import hashlib
import logging
import argparse
import warnings
import textwrap
import traceback
from datetime import datetime, timedelta, date
from pathlib import Path
from typing import Optional, Dict, List, Tuple, Any, Union, Iterator
from dataclasses import dataclass, field, asdict
from collections import defaultdict, OrderedDict, Counter, deque
from functools import lru_cache, wraps
from urllib.parse import urljoin, urlparse, urlencode, quote
from enum import Enum, auto
from contextlib import contextmanager
import threading
import queue
import copy

# third-party
import warnings
warnings.filterwarnings("ignore")

try:
    from playwright.sync_api import sync_playwright, Page, Browser, BrowserContext, Response as PWResponse
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
    import matplotlib.patches as mpatches
    import matplotlib.gridspec as gridspec
    from matplotlib.patches import FancyBboxPatch
    from matplotlib.colors import LinearSegmentedColormap
    import seaborn as sns
    MATPLOTLIB_OK = True
except ImportError:
    MATPLOTLIB_OK = False

try:
    from scipy import stats as scipy_stats
    SCIPY_OK = True
except ImportError:
    SCIPY_OK = False

# ─────────────────────────────────────────────────────────────────────────────
# TERMINAL COLORS — works without rich library
# ─────────────────────────────────────────────────────────────────────────────

class C:
    """ANSI color codes. Auto-disabled on Windows CMD."""
    _ok = sys.stdout.isatty() or os.name != 'nt'

    RESET   = "\033[0m"   if _ok else ""
    BOLD    = "\033[1m"   if _ok else ""
    DIM     = "\033[2m"   if _ok else ""
    ITALIC  = "\033[3m"   if _ok else ""

    BLACK   = "\033[30m"  if _ok else ""
    RED     = "\033[31m"  if _ok else ""
    GREEN   = "\033[32m"  if _ok else ""
    YELLOW  = "\033[33m"  if _ok else ""
    BLUE    = "\033[34m"  if _ok else ""
    MAGENTA = "\033[35m"  if _ok else ""
    CYAN    = "\033[36m"  if _ok else ""
    WHITE   = "\033[37m"  if _ok else ""

    BRED    = "\033[91m"  if _ok else ""
    BGREEN  = "\033[92m"  if _ok else ""
    BYELLOW = "\033[93m"  if _ok else ""
    BBLUE   = "\033[94m"  if _ok else ""
    BMAGENTA= "\033[95m"  if _ok else ""
    BCYAN   = "\033[96m"  if _ok else ""
    BWHITE  = "\033[97m"  if _ok else ""

    BG_RED    = "\033[41m" if _ok else ""
    BG_GREEN  = "\033[42m" if _ok else ""
    BG_YELLOW = "\033[43m" if _ok else ""
    BG_BLUE   = "\033[44m" if _ok else ""

    @staticmethod
    def wrap(text: str, *codes: str) -> str:
        return "".join(codes) + str(text) + C.RESET

    @staticmethod
    def green(t):  return C.wrap(t, C.BGREEN)
    @staticmethod
    def red(t):    return C.wrap(t, C.BRED)
    @staticmethod
    def yellow(t): return C.wrap(t, C.BYELLOW)
    @staticmethod
    def cyan(t):   return C.wrap(t, C.BCYAN)
    @staticmethod
    def magenta(t):return C.wrap(t, C.BMAGENTA)
    @staticmethod
    def bold(t):   return C.wrap(t, C.BOLD)
    @staticmethod
    def dim(t):    return C.wrap(t, C.DIM)
    @staticmethod
    def blue(t):   return C.wrap(t, C.BBLUE)


def _box(lines: List[str], title: str = "", width: int = 70, color=None) -> str:
    """Draw a Unicode box around lines."""
    color = color or C.CYAN
    inner = width - 2
    top    = f"{color}╔{'═' * inner}╗{C.RESET}"
    bottom = f"{color}╚{'═' * inner}╝{C.RESET}"
    result = [top]
    if title:
        padded = f" {title} ".center(inner)
        result.append(f"{color}║{C.BOLD}{padded}{C.RESET}{color}║{C.RESET}")
        result.append(f"{color}╠{'═' * inner}╣{C.RESET}")
    for line in lines:
        # strip ANSI for length calc
        clean = re.sub(r'\033\[[0-9;]*m', '', line)
        pad = inner - len(clean)
        result.append(f"{color}║{C.RESET} {line}{' ' * max(0, pad - 1)}{color}║{C.RESET}")
    result.append(bottom)
    return "\n".join(result)


def _table(headers: List[str], rows: List[List[str]], col_widths: List[int] = None) -> str:
    """Simple terminal table renderer."""
    if not rows:
        return C.dim("  (no data)")

    if not col_widths:
        col_widths = []
        for i, h in enumerate(headers):
            max_w = len(re.sub(r'\033\[[0-9;]*m', '', h))
            for row in rows:
                if i < len(row):
                    cell_len = len(re.sub(r'\033\[[0-9;]*m', '', str(row[i])))
                    max_w = max(max_w, cell_len)
            col_widths.append(min(max_w + 2, 40))

    def make_row(cells, sep="│", pad=" "):
        parts = []
        for i, cell in enumerate(cells):
            w = col_widths[i] if i < len(col_widths) else 10
            clean_len = len(re.sub(r'\033\[[0-9;]*m', '', str(cell)))
            padding = w - clean_len
            parts.append(f"{pad}{cell}{pad * max(0, padding - 1)}")
        return sep + sep.join(parts) + sep

    separator = "├" + "┼".join("─" * (w + 1) for w in col_widths) + "┤"
    top_line  = "┌" + "┬".join("─" * (w + 1) for w in col_widths) + "┐"
    bot_line  = "└" + "┴".join("─" * (w + 1) for w in col_widths) + "┘"

    colored_headers = [C.bold(C.cyan(h)) for h in headers]
    lines = [
        top_line,
        make_row(colored_headers),
        separator,
    ]
    for row in rows:
        lines.append(make_row([str(c) for c in row]))
    lines.append(bot_line)
    return "\n".join(lines)


def _progress_bar(value: float, width: int = 20, show_pct: bool = True) -> str:
    """Render a colored ASCII progress bar."""
    pct = max(0.0, min(100.0, value))
    filled = int(width * pct / 100)
    empty  = width - filled

    if pct >= 75:
        bar_color = C.BGREEN
    elif pct >= 60:
        bar_color = C.BYELLOW
    else:
        bar_color = C.BRED

    bar = f"{bar_color}{'█' * filled}{C.DIM}{'░' * empty}{C.RESET}"
    suffix = f" {bar_color}{pct:.1f}%{C.RESET}" if show_pct else ""
    return f"[{bar}]{suffix}"


def _spinner(msg: str = "Loading"):
    """Simple non-blocking spinner context manager."""
    frames = ["⠋","⠙","⠹","⠸","⠼","⠴","⠦","⠧","⠇","⠏"]
    stop_event = threading.Event()

    def spin():
        i = 0
        while not stop_event.is_set():
            sys.stdout.write(f"\r{C.CYAN}{frames[i % len(frames)]}{C.RESET} {msg}   ")
            sys.stdout.flush()
            time.sleep(0.1)
            i += 1
        sys.stdout.write("\r" + " " * (len(msg) + 10) + "\r")
        sys.stdout.flush()

    t = threading.Thread(target=spin, daemon=True)
    t.start()
    return stop_event


# ─────────────────────────────────────────────────────────────────────────────
# LOGGING
# ─────────────────────────────────────────────────────────────────────────────

class EtLabLogger:
    """Custom logger with emoji + color prefixes. Gen-Z friendly."""

    LEVELS = {"DEBUG": 0, "INFO": 1, "WARN": 2, "ERROR": 3, "CRITICAL": 4}

    def __init__(self, level: str = "INFO", log_file: Optional[Path] = None):
        self.level = self.LEVELS.get(level.upper(), 1)
        self.log_file = log_file
        self._lock = threading.Lock()
        if log_file:
            log_file.parent.mkdir(parents=True, exist_ok=True)

    def _write(self, level: str, emoji: str, color, msg: str):
        if self.LEVELS.get(level, 0) < self.level:
            return
        ts = datetime.now().strftime("%H:%M:%S")
        line = f"{C.dim(ts)} {color(emoji + ' ' + msg)}"
        with self._lock:
            print(line)
            if self.log_file:
                clean = re.sub(r'\033\[[0-9;]*m', '', line)
                with open(self.log_file, "a", encoding="utf-8") as f:
                    f.write(clean + "\n")

    def debug(self, msg):    self._write("DEBUG", "🔍", C.dim, msg)
    def info(self, msg):     self._write("INFO",  "ℹ️ ", C.cyan, msg)
    def success(self, msg):  self._write("INFO",  "✅", C.green, msg)
    def warn(self, msg):     self._write("WARN",  "⚠️ ", C.yellow, msg)
    def error(self, msg):    self._write("ERROR", "❌", C.red, msg)
    def critical(self, msg): self._write("CRITICAL", "💀", C.red, msg)
    def vibe(self, msg):     self._write("INFO",  "🔥", C.magenta, msg)


# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────

BASE_URL    = "https://ukfcet.etlab.app"
OUTPUT_DIR  = Path("etlab_output")
CACHE_DIR   = OUTPUT_DIR / ".cache"
LOG_FILE    = OUTPUT_DIR / "etlab.log"

SAFE_THRESHOLD   = 75.0   # minimum attendance %
DANGER_THRESHOLD = 60.0   # really in trouble zone

# All known endpoint patterns — will be tried in order
ENDPOINT_PATTERNS = {
    "login":              ["/user/login"],
    "dashboard":          ["/user/dashboard", "/dashboard", "/student/dashboard"],
    "profile":            ["/student/profile", "/ktuacademics/student/profile"],
    "attendance_date":    ["/ktuacademics/student/attendance", "/student/attendance"],
    "attendance_subject": [
        "/ktuacademics/student/viewattendancesubject/{batch_id}",
        "/student/viewattendancesubject/{batch_id}",
    ],
    "attendance_month": [
        "/ktuacademics/student/viewsubjectattendancemonth/{batch_id}",
    ],
    "results":     ["/student/results", "/ktuacademics/student/results"],
    "timetable":   ["/student/timetable", "/ktuacademics/student/timetable"],
    "assignments": ["/student/assignments"],
}

# API patterns to intercept (JSON endpoints the frontend might call)
API_INTERCEPT_PATTERNS = [
    r"/api/",
    r"\.json",
    r"/attendance/data",
    r"/student/data",
    r"format=json",
    r"type=json",
]

# Status class name variations across EtLab versions
PRESENT_CLASSES  = {"present", "att_present", "att-present", "p", "green", "success"}
ABSENT_CLASSES   = {"absent", "att_absent", "att-absent", "a", "red", "danger", "failure"}
DUTY_CLASSES     = {"duty", "duty_leave", "dutyleave", "dl", "yellow", "warning", "info"}
MEDICAL_CLASSES  = {"medical", "medical_leave", "ml", "blue", "primary"}


# ─────────────────────────────────────────────────────────────────────────────
# DATA MODELS — Pydantic-style with full validation
# ─────────────────────────────────────────────────────────────────────────────

class AttendanceStatus(Enum):
    PRESENT      = "present"
    ABSENT       = "absent"
    DUTY_LEAVE   = "duty_leave"
    MEDICAL      = "medical_leave"
    HOLIDAY      = "holiday"
    UNKNOWN      = "unknown"

    @classmethod
    def from_classes(cls, class_list: List[str]) -> "AttendanceStatus":
        """Detect status from CSS class list."""
        combined = " ".join(class_list).lower()
        if any(c in combined for c in PRESENT_CLASSES):
            return cls.PRESENT
        if any(c in combined for c in ABSENT_CLASSES):
            return cls.ABSENT
        if any(c in combined for c in DUTY_CLASSES):
            return cls.DUTY_LEAVE
        if any(c in combined for c in MEDICAL_CLASSES):
            return cls.MEDICAL
        if "holiday" in combined:
            return cls.HOLIDAY
        return cls.UNKNOWN

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

    @property
    def counts_as_present(self) -> bool:
        return self in (self.PRESENT, self.DUTY_LEAVE, self.MEDICAL)


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
    Uses mathematical formulae for bunk budget calculations.
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

    # ── computed properties ─────────────────────────────────────────────

    @property
    def effective_present(self) -> int:
        """Present + duty + medical (all count toward attendance)."""
        return self.present + self.duty_leave + self.medical_leave

    @property
    def percentage(self) -> float:
        """Official attendance % (effective / total)."""
        if self.total_classes == 0:
            return 0.0
        return round(self.effective_present / self.total_classes * 100, 2)

    @property
    def raw_percentage(self) -> float:
        """Physical attendance % (only actual present)."""
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
        if self.is_safe:    return "✅"
        if self.is_danger:  return "💀"
        return "⚠️"

    @property
    def classes_to_attend(self) -> int:
        """
        Min classes to attend consecutively to hit 75%.
        Solve: (present + x) / (total + x) >= 0.75
        => x >= (0.75*total - present) / 0.25
        => x >= 3*total - 4*present
        """
        if self.is_safe:
            return 0
        p = self.effective_present
        t = self.total_classes
        needed = math.ceil((0.75 * t - p) / 0.25)
        return max(0, needed)

    @property
    def classes_can_bunk(self) -> int:
        """
        Max classes that can be skipped while staying >= 75%.
        Solve: present / (total + x) >= 0.75
        => x <= present/0.75 - total
        => x <= (4*present - 3*total) / 3
        """
        if not self.is_safe:
            return 0
        p = self.effective_present
        t = self.total_classes
        can = math.floor((4 * p - 3 * t) / 3)
        return max(0, can)

    @property
    def shortage(self) -> int:
        """How many classes short of 75% requirement."""
        if self.is_safe:
            return 0
        required = math.ceil(0.75 * self.total_classes)
        return max(0, required - self.effective_present)

    @property
    def vibe_check(self) -> str:
        """Gen-Z style status message."""
        pct = self.percentage
        if pct == 100:
            return "absolutely unhinged nerd behavior 🤓"
        elif pct >= 90:
            return "professor's favorite fr fr"
        elif pct >= 80:
            return "solid, no cap"
        elif pct >= 75:
            return f"safe but on thin ice 🧊 ({self.classes_can_bunk} bunks left)"
        elif pct >= 65:
            return f"bestie you need to attend {self.classes_to_attend} more rn"
        elif pct >= 50:
            return "bro is cooked 💀 start attending"
        else:
            return "actually cooked. detention speedrun any%"

    def predict_after_n_classes(self, n_total: int, n_attend: int) -> float:
        """
        What-if simulator: predict % after n_total more classes
        assuming you attend n_attend of them.
        """
        new_p = self.effective_present + n_attend
        new_t = self.total_classes + n_total
        return round(new_p / new_t * 100, 2) if new_t > 0 else 0.0

    def weeks_until_safe(self, classes_per_week: int = 6) -> Optional[int]:
        """If at risk, estimate weeks of full attendance to reach 75%."""
        if self.is_safe:
            return 0
        needed = self.classes_to_attend
        if classes_per_week <= 0:
            return None
        return math.ceil(needed / classes_per_week)

    def to_dict(self) -> dict:
        return {
            "code": self.code,
            "name": self.name,
            "total_classes": self.total_classes,
            "present": self.present,
            "absent": self.absent,
            "duty_leave": self.duty_leave,
            "medical_leave": self.medical_leave,
            "effective_present": self.effective_present,
            "percentage": self.percentage,
            "raw_percentage": self.raw_percentage,
            "is_safe": self.is_safe,
            "is_danger": self.is_danger,
            "classes_to_attend": self.classes_to_attend,
            "classes_can_bunk": self.classes_can_bunk,
            "shortage": self.shortage,
            "dates_present": self.dates_present,
            "dates_absent": self.dates_absent,
            "topics": self.topics,
            "vibe_check": self.vibe_check,
        }


@dataclass
class StudentProfile:
    name:           str = ""
    student_id:     str = ""
    roll_number:    str = ""
    department:     str = ""
    semester:       str = ""
    batch:          str = ""
    college:        str = ""
    email:          str = ""
    phone:          str = ""
    batch_id:       str = ""
    student_db_id:  str = ""
    photo_url:      str = ""

    @property
    def display_name(self) -> str:
        return self.name or self.student_id or "Unknown Student"

    @property
    def is_complete(self) -> bool:
        return bool(self.name and self.department)


@dataclass
class ExamResult:
    exam_name:       str
    subject_code:    str
    subject_name:    str
    marks_obtained:  str
    max_marks:       str
    grade:           str
    credits:         str
    result:          str

    @property
    def is_pass(self) -> bool:
        return "pass" in self.result.lower() if self.result else False

    @property
    def grade_points(self) -> float:
        """Convert letter grade to GPA points (KTU scale)."""
        grade_map = {
            "S": 10, "A+": 9, "A": 8.5, "B+": 8,
            "B": 7, "C+": 6.5, "C": 6, "D": 5, "F": 0, "FE": 0
        }
        return grade_map.get(self.grade.upper(), 0.0)


@dataclass
class TimetableSlot:
    day:          str
    period:       int
    subject_code: str
    subject_name: str
    start_time:   str = ""
    end_time:     str = ""
    room:         str = ""


@dataclass
class ScrapedPage:
    """Stores raw page data for debugging."""
    url:        str
    html:       str
    fetched_at: str = field(default_factory=lambda: datetime.now().isoformat())
    method:     str = "playwright"  # playwright | requests
    status:     int = 200

    def save(self, path: Path):
        path.write_text(self.html, encoding="utf-8", errors="replace")


@dataclass
class AcademicData:
    profile:            StudentProfile = field(default_factory=StudentProfile)
    attendance_records: List[AttendanceRecord] = field(default_factory=list)
    subject_attendance: Dict[str, SubjectAttendance] = field(default_factory=dict)
    results:            List[ExamResult] = field(default_factory=list)
    timetable:          List[TimetableSlot] = field(default_factory=list)
    scraped_pages:      Dict[str, ScrapedPage] = field(default_factory=dict)
    api_data:           Dict[str, Any] = field(default_factory=dict)
    scraped_at:         str = field(default_factory=lambda: datetime.now().isoformat())
    errors:             List[str] = field(default_factory=list)

    def add_error(self, msg: str):
        self.errors.append(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}")

    @property
    def has_attendance(self) -> bool:
        return bool(self.subject_attendance)

    @property
    def has_results(self) -> bool:
        return bool(self.results)


# ─────────────────────────────────────────────────────────────────────────────
# DSA UTILITIES — advanced data structures used throughout
# ─────────────────────────────────────────────────────────────────────────────

class LRUCache:
    """
    O(1) get/put LRU Cache using OrderedDict.
    Used to cache parsed pages and avoid re-parsing.
    """
    def __init__(self, capacity: int = 50):
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
    """
    Prefix Trie for fast subject name lookup and fuzzy matching.
    Handles abbreviations like "MATH" → "MATHEMATICS FOR..."
    """
    def __init__(self):
        self._root: Dict = {}
        self._subjects: List[str] = []

    def insert(self, subject: str):
        node = self._root
        for char in subject.upper():
            node = node.setdefault(char, {})
        node["$"] = subject
        self._subjects.append(subject)

    def search_prefix(self, prefix: str) -> List[str]:
        """Return all subjects starting with prefix."""
        node = self._root
        for char in prefix.upper():
            if char not in node:
                return []
            node = node[char]
        return self._collect(node)

    def _collect(self, node: Dict) -> List[str]:
        results = []
        if "$" in node:
            results.append(node["$"])
        for key, child in node.items():
            if key != "$":
                results.extend(self._collect(child))
        return results

    def fuzzy_find(self, query: str, max_results: int = 5) -> List[Tuple[float, str]]:
        """Find closest subjects using edit distance + prefix scoring."""
        scored = []
        q = query.upper()
        for subject in self._subjects:
            s = subject.upper()
            # Levenshtein distance (DP)
            dist = self._levenshtein(q, s[:len(q) + 5])
            # Prefix bonus
            prefix_score = len(os.path.commonprefix([q, s])) / max(len(q), 1)
            score = prefix_score - (dist / max(len(q), len(s), 1)) * 0.5
            scored.append((score, subject))
        scored.sort(reverse=True)
        return scored[:max_results]

    @staticmethod
    def _levenshtein(a: str, b: str) -> int:
        """Standard DP Levenshtein distance O(m*n)."""
        m, n = len(a), len(b)
        dp = list(range(n + 1))
        for i in range(1, m + 1):
            prev = dp[:]
            dp[0] = i
            for j in range(1, n + 1):
                cost = 0 if a[i-1] == b[j-1] else 1
                dp[j] = min(dp[j] + 1, dp[j-1] + 1, prev[j-1] + cost)
        return dp[n]


class MinHeap:
    """
    Min-heap wrapper for priority-queue operations.
    Used to rank subjects by risk level (lowest attendance = highest priority).
    """
    def __init__(self):
        self._heap: List[Tuple] = []

    def push(self, priority: float, item: Any):
        heapq.heappush(self._heap, (priority, id(item), item))

    def pop(self) -> Tuple[float, Any]:
        priority, _, item = heapq.heappop(self._heap)
        return priority, item

    def peek(self) -> Optional[Tuple[float, Any]]:
        if self._heap:
            return self._heap[0][0], self._heap[0][2]
        return None

    def __len__(self):
        return len(self._heap)

    def to_sorted_list(self) -> List[Tuple[float, Any]]:
        return [(p, item) for p, _, item in sorted(self._heap)]


class Graph:
    """
    Adjacency list graph for subject → topic dependency mapping.
    Can detect which subjects share topics (useful for exam planning).
    Uses BFS/DFS for traversal.
    """
    def __init__(self):
        self._adj: Dict[str, List[str]] = defaultdict(list)
        self._nodes: set = set()

    def add_edge(self, u: str, v: str):
        self._adj[u].append(v)
        self._nodes.update([u, v])

    def bfs(self, start: str) -> List[str]:
        visited, result = {start}, [start]
        q = deque([start])
        while q:
            node = q.popleft()
            for neighbor in self._adj[node]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    result.append(neighbor)
                    q.append(neighbor)
        return result

    def connected_components(self) -> List[List[str]]:
        visited = set()
        components = []
        for node in self._nodes:
            if node not in visited:
                component = self.bfs(node)
                components.append(component)
                visited.update(component)
        return components


class RingBuffer:
    """
    Fixed-size circular buffer for storing last N attendance events.
    O(1) append, used for recent attendance streak tracking.
    """
    def __init__(self, size: int):
        self._buf: List[Optional[Any]] = [None] * size
        self._size = size
        self._pos = 0
        self._count = 0

    def append(self, item: Any):
        self._buf[self._pos % self._size] = item
        self._pos += 1
        self._count = min(self._count + 1, self._size)

    def to_list(self) -> List[Any]:
        if self._count < self._size:
            return [x for x in self._buf[:self._count] if x is not None]
        start = self._pos % self._size
        return self._buf[start:] + self._buf[:start]

    @property
    def streak(self) -> int:
        """Consecutive present count from most recent."""
        items = self.to_list()
        count = 0
        for item in reversed(items):
            if item == AttendanceStatus.PRESENT:
                count += 1
            else:
                break
        return count


# ─────────────────────────────────────────────────────────────────────────────
# CACHE MANAGER — disk + memory caching
# ─────────────────────────────────────────────────────────────────────────────

class CacheManager:
    """
    Two-level cache: LRU in memory + JSON on disk.
    Cache key = SHA256 of URL + date (so cache invalidates daily).
    """
    def __init__(self, cache_dir: Path, ttl_hours: int = 6):
        self._dir = cache_dir
        self._ttl = timedelta(hours=ttl_hours)
        self._mem = LRUCache(capacity=100)
        self._dir.mkdir(parents=True, exist_ok=True)

    def _key(self, url: str) -> str:
        day = datetime.now().strftime("%Y-%m-%d")
        return hashlib.sha256(f"{url}:{day}".encode()).hexdigest()[:16]

    def _path(self, key: str) -> Path:
        return self._dir / f"{key}.json"

    def get(self, url: str) -> Optional[str]:
        key = self._key(url)
        # Level 1: memory
        cached = self._mem.get(key)
        if cached:
            return cached
        # Level 2: disk
        p = self._path(key)
        if p.exists():
            try:
                data = json.loads(p.read_text())
                stored_at = datetime.fromisoformat(data["stored_at"])
                if datetime.now() - stored_at < self._ttl:
                    self._mem.put(key, data["html"])
                    return data["html"]
            except Exception:
                pass
        return None

    def set(self, url: str, html: str):
        key = self._key(url)
        self._mem.put(key, html)
        p = self._path(key)
        try:
            p.write_text(json.dumps({"html": html, "stored_at": datetime.now().isoformat()}))
        except Exception:
            pass

    def clear(self):
        for f in self._dir.glob("*.json"):
            f.unlink(missing_ok=True)
        self._mem = LRUCache()


# ─────────────────────────────────────────────────────────────────────────────
# PLAYWRIGHT ENGINE — the real deal
# ─────────────────────────────────────────────────────────────────────────────

class PlaywrightEngine:
    """
    Playwright-based browser engine.
    - Real Chromium browser → bypasses JS rendering
    - Intercepts all network requests → catches hidden JSON APIs
    - Handles Cloudflare (real browser = not flagged)
    - Auto-detects encoding issues (Malayalam etc.)
    - Retry logic on navigation failures
    """

    def __init__(self, log: EtLabLogger, headless: bool = True, slow_mo: int = 0):
        self.log = log
        self.headless = headless
        self.slow_mo = slow_mo
        self._playwright = None
        self._browser: Optional[Browser] = None
        self._context: Optional[BrowserContext] = None
        self._page: Optional[Page] = None
        self._intercepted_api: Dict[str, Any] = {}
        self._cache = CacheManager(CACHE_DIR)

    def start(self):
        """Launch browser."""
        if not PLAYWRIGHT_OK:
            raise RuntimeError("Playwright not installed. Run: pip install playwright && playwright install chromium")
        self.log.info("Launching browser engine 🚀")
        self._playwright = sync_playwright().start()
        self._browser = self._playwright.chromium.launch(
            headless=self.headless,
            slow_mo=self.slow_mo,
            args=[
                "--no-sandbox",
                "--disable-blink-features=AutomationControlled",
                "--disable-infobars",
                "--disable-dev-shm-usage",
                "--disable-extensions",
            ],
        )
        self._context = self._browser.new_context(
            viewport={"width": 1366, "height": 768},
            user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
            locale="en-IN",
            timezone_id="Asia/Kolkata",
            java_script_enabled=True,
            accept_downloads=False,
            ignore_https_errors=True,
        )
        # Anti-detection: hide navigator.webdriver
        self._context.add_init_script("""
            Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
            Object.defineProperty(navigator, 'languages', {get: () => ['en-IN', 'en']});
            Object.defineProperty(navigator, 'plugins', {get: () => [1,2,3,4,5]});
        """)
        self._page = self._context.new_page()
        self._setup_intercept()
        self.log.success("Browser ready")

    def _setup_intercept(self):
        """Intercept network responses to catch JSON APIs."""
        def on_response(response: PWResponse):
            try:
                ct = response.headers.get("content-type", "")
                url = response.url
                if "json" in ct or any(re.search(p, url) for p in API_INTERCEPT_PATTERNS):
                    try:
                        body = response.json()
                        self._intercepted_api[url] = body
                        self.log.debug(f"Intercepted API: {url[:80]}")
                    except Exception:
                        pass
            except Exception:
                pass

        self._page.on("response", on_response)

    def stop(self):
        """Close browser cleanly."""
        try:
            if self._context:
                self._context.close()
            if self._browser:
                self._browser.close()
            if self._playwright:
                self._playwright.stop()
        except Exception:
            pass

    def navigate(self, url: str, wait: str = "networkidle", timeout: int = 30000,
                 retries: int = 3) -> Optional[str]:
        """
        Navigate to URL and return rendered HTML.
        Falls back through multiple wait strategies.
        Retries on timeout.
        """
        # Check cache first
        cached = self._cache.get(url)
        if cached:
            self.log.debug(f"Cache hit: {url[:60]}")
            return cached

        wait_strategies = [wait, "domcontentloaded", "load", "commit"]

        for attempt in range(retries):
            for strategy in wait_strategies:
                try:
                    self._page.goto(url, wait_until=strategy, timeout=timeout)
                    # Extra wait for dynamic content
                    try:
                        self._page.wait_for_timeout(1500)
                    except Exception:
                        pass
                    html = self._page.content()
                    if html and len(html) > 500:
                        self._cache.set(url, html)
                        return html
                except Exception as e:
                    if "timeout" not in str(e).lower() and attempt == retries - 1:
                        self.log.warn(f"Navigation error ({strategy}): {e}")
                    continue

            # Exponential backoff between retries
            if attempt < retries - 1:
                wait_time = (2 ** attempt) + 1
                self.log.warn(f"Retry {attempt + 1}/{retries} in {wait_time}s...")
                time.sleep(wait_time)

        self.log.error(f"Failed to navigate to {url[:60]} after {retries} retries")
        return None

    def get_cookies(self) -> List[dict]:
        return self._context.cookies() if self._context else []

    def get_current_url(self) -> str:
        try:
            return self._page.url
        except Exception:
            return ""

    def fill_and_submit(self, selector: str, value: str):
        """Fill a form field safely."""
        try:
            self._page.wait_for_selector(selector, timeout=5000)
            self._page.fill(selector, value)
        except Exception as e:
            self.log.warn(f"Could not fill {selector}: {e}")

    def click(self, selector: str, timeout: int = 5000):
        """Click an element safely."""
        try:
            self._page.wait_for_selector(selector, timeout=timeout)
            self._page.click(selector)
        except Exception as e:
            self.log.warn(f"Could not click {selector}: {e}")

    def screenshot(self, path: Path):
        """Save a screenshot for debugging."""
        try:
            self._page.screenshot(path=str(path), full_page=True)
        except Exception:
            pass

    @property
    def intercepted_api_data(self) -> Dict[str, Any]:
        return copy.deepcopy(self._intercepted_api)


# ─────────────────────────────────────────────────────────────────────────────
# AUTHENTICATION
# ─────────────────────────────────────────────────────────────────────────────

class EtLabAuth:
    """
    Multi-strategy login handler.
    Strategy 1: Standard form submit (CSS selectors)
    Strategy 2: Try multiple input name patterns
    Strategy 3: JavaScript injection login
    Strategy 4: Direct POST simulation
    """

    LOGIN_FIELD_PATTERNS = [
        ('input[name="LoginForm[username]"]', 'input[name="LoginForm[password]"]'),
        ('input[name="username"]',            'input[name="password"]'),
        ('input[type="text"]',                'input[type="password"]'),
        ('#LoginForm_username',               '#LoginForm_password'),
        ('input[id*="username"]',             'input[id*="password"]'),
    ]

    SUBMIT_PATTERNS = [
        'input[type="submit"]',
        'button[type="submit"]',
        'button:has-text("Login")',
        'button:has-text("Sign In")',
        '.btn-primary',
    ]

    def __init__(self, engine: PlaywrightEngine, log: EtLabLogger):
        self.engine = engine
        self.log = log
        self.logged_in = False

    def login(self, username: str, password: str, max_attempts: int = 3) -> bool:
        """Attempt login with multiple strategies."""
        login_url = urljoin(BASE_URL, "/user/login")

        for attempt in range(1, max_attempts + 1):
            self.log.info(f"Login attempt {attempt}/{max_attempts}...")
            html = self.engine.navigate(login_url, wait="domcontentloaded")

            if not html:
                self.log.error("Could not load login page")
                continue

            # Save debug screenshot
            self.engine.screenshot(OUTPUT_DIR / "debug_login.png")

            # Try each field pattern
            success = False
            for user_sel, pass_sel in self.LOGIN_FIELD_PATTERNS:
                try:
                    page = self.engine._page
                    user_el = page.query_selector(user_sel)
                    pass_el = page.query_selector(pass_sel)
                    if user_el and pass_el:
                        user_el.fill("")
                        user_el.type(username, delay=50)
                        pass_el.fill("")
                        pass_el.type(password, delay=50)
                        self.log.debug(f"Filled fields: {user_sel}, {pass_sel}")

                        # Try each submit button
                        for submit_sel in self.SUBMIT_PATTERNS:
                            btn = page.query_selector(submit_sel)
                            if btn:
                                btn.click()
                                break
                        else:
                            # Fallback: press Enter
                            pass_el.press("Enter")

                        # Wait for navigation
                        try:
                            page.wait_for_load_state("networkidle", timeout=10000)
                        except Exception:
                            page.wait_for_timeout(3000)

                        current_url = self.engine.get_current_url()
                        if "login" not in current_url.lower():
                            self.log.success(f"Login successful! → {current_url}")
                            self.logged_in = True
                            return True

                        # Check for error message on page
                        page_text = page.inner_text("body") if page else ""
                        if any(kw in page_text.lower() for kw in ["invalid", "incorrect", "wrong", "error"]):
                            self.log.error("Wrong credentials. Check username/password.")
                            return False

                        success = True
                        break
                except Exception as e:
                    self.log.debug(f"Field pattern {user_sel} failed: {e}")
                    continue

            if not success:
                # Strategy: JavaScript injection
                self.log.warn("Trying JS injection login...")
                try:
                    self.engine._page.evaluate(f"""
                        () => {{
                            let inputs = document.querySelectorAll('input[type="text"], input[type="email"]');
                            let passes = document.querySelectorAll('input[type="password"]');
                            if (inputs.length > 0) inputs[0].value = '{username}';
                            if (passes.length > 0) passes[0].value = '{password}';
                            let form = document.querySelector('form');
                            if (form) form.submit();
                        }}
                    """)
                    self.engine._page.wait_for_timeout(3000)
                    current_url = self.engine.get_current_url()
                    if "login" not in current_url.lower():
                        self.log.success("JS login worked!")
                        self.logged_in = True
                        return True
                except Exception as e:
                    self.log.warn(f"JS injection failed: {e}")

            # Backoff between attempts
            if attempt < max_attempts:
                time.sleep(3 * attempt)

        self.log.error("All login strategies failed.")
        return False

    def verify_session(self) -> bool:
        """Check if still logged in."""
        url = self.engine.get_current_url()
        return bool(url) and "login" not in url.lower()


# ─────────────────────────────────────────────────────────────────────────────
# HTML PARSER — handles multiple EtLab HTML versions
# ─────────────────────────────────────────────────────────────────────────────

class EtLabParser:
    """
    Robust multi-strategy HTML parser.
    Each parse method tries multiple approaches and picks the best result.
    """

    def __init__(self, log: EtLabLogger):
        self.log = log
        self._subject_trie = Trie()

    @staticmethod
    def _soup(html: str) -> BeautifulSoup:
        """Parse HTML with best available parser."""
        for parser in ["lxml", "html.parser", "html5lib"]:
            try:
                return BeautifulSoup(html, parser)
            except Exception:
                continue
        return BeautifulSoup(html, "html.parser")

    @staticmethod
    def _clean(text: str) -> str:
        """Normalize whitespace and encoding artifacts."""
        if not text:
            return ""
        text = re.sub(r'\s+', ' ', text).strip()
        text = text.replace('\xa0', ' ').replace('\u00a0', ' ')
        return text

    @staticmethod
    def _extract_numbers(text: str) -> List[int]:
        """Extract all integers from text."""
        return [int(m) for m in re.findall(r'\b(\d+)\b', text)]

    @staticmethod
    def _detect_cell_status(cell: Tag) -> AttendanceStatus:
        """
        Multi-strategy cell status detection:
        1. CSS classes
        2. Background color (style attr)
        3. Text content
        4. Title/tooltip attribute
        """
        if not cell:
            return AttendanceStatus.UNKNOWN

        classes = cell.get("class") or []
        status = AttendanceStatus.from_classes(classes)
        if status != AttendanceStatus.UNKNOWN:
            return status

        # Check style for background color hints
        style = cell.get("style", "").lower()
        if "green" in style or "#0f0" in style or "success" in style:
            return AttendanceStatus.PRESENT
        if "red" in style or "danger" in style or "#f00" in style:
            return AttendanceStatus.ABSENT

        # Check title/tooltip
        title = (cell.get("title") or cell.get("data-original-title") or "").lower()
        if "present" in title:     return AttendanceStatus.PRESENT
        if "absent" in title:      return AttendanceStatus.ABSENT
        if "duty" in title:        return AttendanceStatus.DUTY_LEAVE
        if "medical" in title:     return AttendanceStatus.MEDICAL

        # Check text
        text = cell.get_text(strip=True).lower()
        if text in ("p", "present"):  return AttendanceStatus.PRESENT
        if text in ("a", "absent"):   return AttendanceStatus.ABSENT
        if text in ("dl", "duty"):    return AttendanceStatus.DUTY_LEAVE
        if text in ("ml", "medical"): return AttendanceStatus.MEDICAL

        return AttendanceStatus.UNKNOWN

    def parse_subject_from_cell(self, cell: Tag) -> Tuple[str, str, str]:
        """
        Extract (code, name, topic) from a table cell.
        Handles multiple formats:
        - "25DSBST201 - MATHEMATICS..."
        - Just subject name
        - Code in one element, name in another
        """
        if not cell:
            return "", "", ""

        anchor = cell.find("a")
        el = anchor if anchor else cell

        # Get main text (not in spans)
        main_text = ""
        for content in el.children:
            if isinstance(content, NavigableString) and content.strip():
                main_text = self._clean(str(content))
                break

        if not main_text:
            main_text = self._clean(el.get_text())

        # Get topic from span (tooltip)
        span = el.find("span")
        topic = self._clean(span.get_text()) if span else ""

        # Parse code - name
        patterns = [
            r"^([A-Z0-9]{6,})\s*[-–:]\s*(.+)$",
            r"^(\w+\d+\w*)\s+(.+)$",
        ]
        for pattern in patterns:
            m = re.match(pattern, main_text, re.IGNORECASE)
            if m:
                return m.group(1).strip(), m.group(2).strip(), topic

        return "", main_text, topic

    def parse_attendance_page(self, html: str) -> Tuple[List[AttendanceRecord], str, str]:
        """
        Parse attendance page with 3 strategies:
        1. Standard EtLab table format
        2. Alternate CSS class format
        3. Generic table format
        Returns (records, month_pct, overall_pct)
        """
        soup = self._soup(html)
        records = []
        month_pct = ""
        overall_pct = ""

        # Try to find percentage summaries first
        for el in soup.find_all(string=re.compile(r'\d+\.?\d*\s*%')):
            text = str(el)
            if "month" in text.lower():
                m = re.search(r'(\d+\.?\d*)\s*%', text)
                if m:
                    month_pct = m.group(1) + "%"
            if any(w in text.lower() for w in ["overall", "till", "total"]):
                m = re.search(r'(\d+\.?\d*)\s*%', text)
                if m:
                    overall_pct = m.group(1) + "%"

        # Strategy 1: Standard EtLab table
        main_table = soup.find("table")
        if main_table:
            records = self._parse_standard_table(main_table)

        # Strategy 2: Multiple tables (subject-per-table layout)
        if not records:
            all_tables = soup.find_all("table")
            for table in all_tables:
                r = self._parse_standard_table(table)
                records.extend(r)

        # Strategy 3: Div-based layout
        if not records:
            records = self._parse_div_layout(soup)

        self.log.debug(f"Parsed {len(records)} attendance records")
        return records, month_pct, overall_pct

    def _parse_standard_table(self, table: Tag) -> List[AttendanceRecord]:
        """Parse standard EtLab date-row attendance table."""
        records = []
        rows = table.find_all("tr")
        if len(rows) < 2:
            return records

        for row in rows:
            # Date cell is usually in <th>
            date_cell = row.find("th")
            if not date_cell:
                continue

            date_text = self._clean(date_cell.get_text())
            if not date_text or not re.search(r'\d', date_text):
                continue

            # Skip holiday / weekend rows
            row_classes = row.get("class") or []
            if any(c in " ".join(row_classes).lower() for c in ["holiday", "sunday", "weekend"]):
                continue
            if "sun" in " ".join(row_classes).lower():
                continue

            cells = row.find_all("td")
            for period_idx, cell in enumerate(cells, start=1):
                status = self._detect_cell_status(cell)
                if status in (AttendanceStatus.UNKNOWN, AttendanceStatus.HOLIDAY):
                    continue

                code, name, topic = self.parse_subject_from_cell(cell)
                if not name and not code:
                    continue

                records.append(AttendanceRecord(
                    date=date_text,
                    day_of_week="",
                    subject_code=code,
                    subject_name=name,
                    status=status,
                    period=period_idx,
                    topic=topic,
                    raw_class=" ".join(cell.get("class") or []),
                ))

        return records

    def _parse_div_layout(self, soup: BeautifulSoup) -> List[AttendanceRecord]:
        """Fallback: parse div-based attendance cards."""
        records = []
        # Look for attendance card-style divs
        cards = soup.find_all("div", class_=re.compile(r"attend|card|item", re.I))
        for card in cards:
            status_classes = card.get("class") or []
            status = AttendanceStatus.from_classes(status_classes)
            if status == AttendanceStatus.UNKNOWN:
                continue

            date_el = card.find(class_=re.compile(r"date|day", re.I))
            date_text = self._clean(date_el.get_text()) if date_el else ""

            subject_el = card.find(class_=re.compile(r"subject|course|name", re.I))
            name = self._clean(subject_el.get_text()) if subject_el else ""

            if name:
                records.append(AttendanceRecord(
                    date=date_text, day_of_week="",
                    subject_code="", subject_name=name,
                    status=status, period=0,
                ))
        return records

    def parse_subject_summary(self, html: str) -> Dict[str, SubjectAttendance]:
        """Parse subject-wise attendance summary page."""
        soup = self._soup(html)
        subjects: Dict[str, SubjectAttendance] = {}

        for table in soup.find_all("table"):
            rows = table.find_all("tr")
            if len(rows) < 2:
                continue

            # Detect column layout from header
            header_row = rows[0]
            headers = [self._clean(c.get_text()).lower() for c in header_row.find_all(["th", "td"])]

            # Find column indices
            col_map = {}
            for i, h in enumerate(headers):
                if "subject" in h and "code" in h:        col_map["code"] = i
                elif "subject" in h and "name" in h:      col_map["name"] = i
                elif "subject" in h:                       col_map.setdefault("name", i)
                elif "total" in h or "conducted" in h:    col_map["total"] = i
                elif "present" in h:                       col_map["present"] = i
                elif "absent" in h:                        col_map["absent"] = i
                elif "duty" in h:                          col_map["duty"] = i
                elif "medical" in h:                       col_map["medical"] = i
                elif "%" in h or "percent" in h:           col_map["pct"] = i

            if not col_map:
                continue

            for row in rows[1:]:
                cells = row.find_all(["td", "th"])
                if not cells:
                    continue
                texts = [self._clean(c.get_text()) for c in cells]
                if not any(texts):
                    continue

                # Extract subject name/code
                name_col = col_map.get("name", 0)
                code_col = col_map.get("code", -1)

                subject_text = texts[name_col] if name_col < len(texts) else ""
                if not subject_text:
                    continue

                # Try to parse code from subject text
                code = texts[code_col] if code_col >= 0 and code_col < len(texts) else ""
                if not code:
                    m = re.match(r"^([A-Z0-9]{4,})\s*[-–:]\s*(.+)$", subject_text)
                    if m:
                        code, subject_text = m.group(1), m.group(2)

                sa = SubjectAttendance(code=code, name=subject_text)

                # Fill numeric fields
                def safe_int(col_key: str) -> int:
                    idx = col_map.get(col_key, -1)
                    if idx < 0 or idx >= len(texts):
                        return 0
                    nums = self._extract_numbers(texts[idx])
                    return nums[0] if nums else 0

                sa.total_classes = safe_int("total")
                sa.present       = safe_int("present")
                sa.absent        = safe_int("absent")
                sa.duty_leave    = safe_int("duty")
                sa.medical_leave = safe_int("medical")

                if sa.total_classes > 0 or sa.present > 0:
                    subjects[subject_text] = sa
                    self._subject_trie.insert(subject_text)

        return subjects

    def parse_profile(self, html: str) -> StudentProfile:
        """Multi-strategy profile parser."""
        soup = self._soup(html)
        profile = StudentProfile()

        # Strategy 1: Table key-value pairs
        for table in soup.find_all("table"):
            for row in table.find_all("tr"):
                cells = row.find_all(["td", "th"])
                if len(cells) < 2:
                    continue
                key = self._clean(cells[0].get_text()).lower()
                val = self._clean(cells[1].get_text())

                field_map = {
                    "name": "name", "student name": "name",
                    "roll": "roll_number", "register": "roll_number",
                    "department": "department", "branch": "department", "dept": "department",
                    "semester": "semester", "sem": "semester",
                    "batch": "batch",
                    "email": "email",
                    "phone": "phone", "mobile": "phone",
                    "college": "college", "institution": "college",
                }
                for k, attr in field_map.items():
                    if k in key and not getattr(profile, attr):
                        setattr(profile, attr, val)

        # Strategy 2: Definition list (dl/dt/dd)
        if not profile.name:
            for dl in soup.find_all("dl"):
                dts = dl.find_all("dt")
                dds = dl.find_all("dd")
                for dt, dd in zip(dts, dds):
                    key = self._clean(dt.get_text()).lower()
                    val = self._clean(dd.get_text())
                    if "name" in key:
                        profile.name = val

        # Strategy 3: Extract from page title or h-tags
        if not profile.name:
            for tag in soup.find_all(["h1", "h2", "h3", "h4"]):
                text = self._clean(tag.get_text())
                if text and 3 < len(text) < 60:
                    skip_words = ["dashboard", "profile", "etlab", "menu", "home", "login", "logout"]
                    if not any(w in text.lower() for w in skip_words):
                        profile.name = text
                        break

        # Strategy 4: Meta tags
        if not profile.name:
            meta_title = soup.find("title")
            if meta_title:
                title = meta_title.get_text()
                parts = re.split(r'[-|–—]', title)
                if parts:
                    name_candidate = self._clean(parts[0])
                    if name_candidate and not any(w in name_candidate.lower() for w in ["etlab", "login"]):
                        profile.name = name_candidate

        return profile

    def parse_results(self, html: str) -> List[ExamResult]:
        """Parse exam results page."""
        soup = self._soup(html)
        results = []

        for table in soup.find_all("table"):
            rows = table.find_all("tr")
            if len(rows) < 2:
                continue
            headers = [self._clean(c.get_text()).lower() for c in rows[0].find_all(["th", "td"])]
            if not any(kw in " ".join(headers) for kw in ["subject", "grade", "marks", "result"]):
                continue

            for row in rows[1:]:
                cells = row.find_all(["td", "th"])
                texts = [self._clean(c.get_text()) for c in cells]
                if not texts or all(not t for t in texts):
                    continue

                result = ExamResult(
                    exam_name="", subject_code="", subject_name="",
                    marks_obtained="", max_marks="", grade="", credits="", result=""
                )
                for i, header in enumerate(headers):
                    if i >= len(texts):
                        break
                    v = texts[i]
                    if "code" in header:          result.subject_code = v
                    elif "name" in header:        result.subject_name = v
                    elif "subject" in header and not result.subject_name:
                        m = re.match(r"^([A-Z0-9]+)\s*[-:]\s*(.+)$", v)
                        if m:
                            result.subject_code, result.subject_name = m.group(1), m.group(2)
                        else:
                            result.subject_name = v
                    elif "grade" in header:       result.grade = v
                    elif "credit" in header:      result.credits = v
                    elif "mark" in header or "score" in header:
                        if not result.marks_obtained: result.marks_obtained = v
                        else: result.max_marks = v
                    elif "result" in header or "status" in header:
                        result.result = v

                if result.subject_name or result.subject_code:
                    results.append(result)

        return results

    def parse_timetable(self, html: str) -> List[TimetableSlot]:
        """Parse timetable page."""
        soup = self._soup(html)
        slots = []
        DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]

        for table in soup.find_all("table"):
            rows = table.find_all("tr")
            if len(rows) < 2:
                continue
            header_cells = rows[0].find_all(["th", "td"])
            period_headers = [self._clean(c.get_text()) for c in header_cells]

            for row_idx, row in enumerate(rows[1:]):
                cells = row.find_all(["td", "th"])
                if not cells:
                    continue
                day_text = self._clean(cells[0].get_text())
                day = next((d for d in DAYS if d.lower() in day_text.lower()),
                           DAYS[row_idx] if row_idx < len(DAYS) else f"Day {row_idx+1}")

                for col_idx, cell in enumerate(cells[1:], start=1):
                    text = self._clean(cell.get_text())
                    if not text or text in ("-", "—", ""):
                        continue
                    m = re.match(r"^([A-Z0-9]+)\s*[-:]\s*(.+)$", text)
                    code = m.group(1) if m else ""
                    name = m.group(2) if m else text
                    th = period_headers[col_idx] if col_idx < len(period_headers) else ""
                    tm = re.search(r"(\d+:\d+)\s*[-–]\s*(\d+:\d+)", th)
                    slots.append(TimetableSlot(
                        day=day, period=col_idx,
                        subject_code=code, subject_name=name,
                        start_time=tm.group(1) if tm else "",
                        end_time=tm.group(2) if tm else "",
                    ))

        return slots

    def discover_batch_id(self, html: str) -> Tuple[str, str, str]:
        """
        Extract batch_id, encoded batch_id, and student_db_id from HTML.
        Tries multiple regex patterns for different EtLab versions.
        Returns (batch_id, batch_id_enc, student_db_id)
        """
        soup = self._soup(html)
        batch_id = batch_id_enc = student_db_id = ""

        all_hrefs = [a.get("href", "") for a in soup.find_all("a", href=True)]
        all_hrefs += [form.get("action", "") for form in soup.find_all("form")]

        # Also check JS variables in script tags
        all_scripts = " ".join(s.get_text() for s in soup.find_all("script"))

        patterns = [
            (r'/(\d{3,})', 'batch_id'),
            (r'batch_id[=:/](\w+)', 'batch_id_enc'),
            (r'/medicalleave/(\d+)', 'student_db_id'),
            (r'/student/(\d+)', 'student_db_id'),
            (r'student_id[=:/](\d+)', 'student_db_id'),
        ]

        sources = all_hrefs + [all_scripts]

        for source in sources:
            if not source:
                continue
            for pattern, field in patterns:
                m = re.search(pattern, source)
                if m:
                    val = m.group(1)
                    if field == 'batch_id' and not batch_id and len(val) >= 3:
                        batch_id = val
                    elif field == 'batch_id_enc' and not batch_id_enc:
                        batch_id_enc = val
                    elif field == 'student_db_id' and not student_db_id:
                        student_db_id = val

        # Also check JS
        for pattern, field in [
            (r'batchId["\s:=]+["\']?(\d+)', 'batch_id'),
            (r'batch_id["\s:=]+["\']?(\w+)', 'batch_id'),
            (r'studentId["\s:=]+["\']?(\d+)', 'student_db_id'),
        ]:
            m = re.search(pattern, all_scripts)
            if m:
                val = m.group(1)
                if field == 'batch_id' and not batch_id:
                    batch_id = val
                elif field == 'student_db_id' and not student_db_id:
                    student_db_id = val

        return batch_id, batch_id_enc, student_db_id


# ─────────────────────────────────────────────────────────────────────────────
# MAIN SCRAPER ORCHESTRATOR
# ─────────────────────────────────────────────────────────────────────────────

class EtLabScraper:
    """
    Main scraper that orchestrates everything:
    1. Launch Playwright
    2. Login
    3. Discover IDs
    4. Scrape all pages
    5. Check for intercepted APIs (best case)
    6. Parse HTML as fallback
    7. Consolidate into AcademicData
    """

    def __init__(self, username: str, password: str, headless: bool = True,
                 no_cache: bool = False, log: EtLabLogger = None):
        self.username = username
        self.password = password
        self.log = log or EtLabLogger()
        self.engine = PlaywrightEngine(self.log, headless=headless)
        self.auth = EtLabAuth(self.engine, self.log)
        self.parser = EtLabParser(self.log)
        self.data = AcademicData()
        self.data.profile.student_id = username
        self._batch_id = ""
        self._batch_id_enc = ""
        self._student_db_id = ""
        if no_cache:
            CacheManager(CACHE_DIR).clear()

    def _url(self, path: str) -> str:
        return urljoin(BASE_URL, path)

    def _try_endpoints(self, endpoint_key: str, **fmt_kwargs) -> Optional[str]:
        """Try multiple endpoint patterns, return first successful HTML."""
        patterns = ENDPOINT_PATTERNS.get(endpoint_key, [])
        for pattern in patterns:
            try:
                path = pattern.format(**{
                    "batch_id": self._batch_id,
                    "batch_id_enc": self._batch_id_enc,
                    "student_id": self._student_db_id,
                    **fmt_kwargs,
                })
            except KeyError:
                continue

            url = self._url(path)
            spinner = _spinner(f"Fetching {endpoint_key}")
            html = self.engine.navigate(url)
            spinner.set()

            if html and len(html) > 1000:
                # Check we didn't get redirected to login
                current = self.engine.get_current_url()
                if "login" in current.lower():
                    self.log.warn(f"Session expired while fetching {endpoint_key}")
                    return None

                self.data.scraped_pages[endpoint_key] = ScrapedPage(
                    url=url, html=html, method="playwright"
                )
                # Save debug HTML
                (OUTPUT_DIR / f"debug_{endpoint_key}.html").write_text(
                    html, encoding="utf-8", errors="replace"
                )
                self.log.success(f"Got {endpoint_key} ({len(html):,} bytes)")
                return html

        self.log.warn(f"All endpoints failed for: {endpoint_key}")
        return None

    def _update_ids(self, html: str):
        """Update batch/student IDs from any page HTML."""
        bid, benc, sid = self.parser.discover_batch_id(html)
        if bid and not self._batch_id:
            self._batch_id = bid
            self.log.info(f"Found batch_id: {bid}")
        if benc and not self._batch_id_enc:
            self._batch_id_enc = benc
        if sid and not self._student_db_id:
            self._student_db_id = sid
            self.log.info(f"Found student_db_id: {sid}")

        self.data.profile.batch_id = self._batch_id
        self.data.profile.student_db_id = self._student_db_id

    def _check_api_intercepts(self) -> bool:
        """
        Check if Playwright intercepted any JSON attendance APIs.
        If yes, parse those directly — much cleaner than HTML.
        """
        api_data = self.engine.intercepted_api_data
        if not api_data:
            return False

        self.data.api_data = api_data
        found_attendance = False

        for url, payload in api_data.items():
            self.log.info(f"Checking intercepted API: {url[:60]}")

            # Try to parse attendance from API response
            if isinstance(payload, list):
                records = self._parse_api_attendance_list(payload)
                if records:
                    self.data.attendance_records.extend(records)
                    found_attendance = True

            elif isinstance(payload, dict):
                # Check common keys
                for key in ["attendance", "data", "records", "list", "result"]:
                    if key in payload and isinstance(payload[key], list):
                        records = self._parse_api_attendance_list(payload[key])
                        if records:
                            self.data.attendance_records.extend(records)
                            found_attendance = True

        if found_attendance:
            self.log.success(f"Parsed {len(self.data.attendance_records)} records from API intercept!")
        return found_attendance

    def _parse_api_attendance_list(self, items: List[dict]) -> List[AttendanceRecord]:
        """Parse attendance from a JSON list (API response)."""
        records = []
        for item in items:
            if not isinstance(item, dict):
                continue
            # Flexible key matching
            status_val = (
                item.get("status") or item.get("attendance_status") or
                item.get("present") or item.get("type") or ""
            )
            subject = (
                item.get("subject_name") or item.get("subject") or
                item.get("course_name") or item.get("name") or ""
            )
            date = (
                item.get("date") or item.get("attendance_date") or
                item.get("class_date") or ""
            )

            if not subject:
                continue

            status_str = str(status_val).lower()
            if "present" in status_str or status_val == 1 or status_val is True:
                status = AttendanceStatus.PRESENT
            elif "absent" in status_str or status_val == 0 or status_val is False:
                status = AttendanceStatus.ABSENT
            elif "duty" in status_str:
                status = AttendanceStatus.DUTY_LEAVE
            elif "medical" in status_str:
                status = AttendanceStatus.MEDICAL
            else:
                continue

            records.append(AttendanceRecord(
                date=str(date),
                day_of_week="",
                subject_code=item.get("subject_code", ""),
                subject_name=str(subject),
                status=status,
                period=item.get("period", 0),
                topic=item.get("topic", ""),
            ))
        return records

    def scrape_all(self) -> AcademicData:
        """Master scrape method."""
        OUTPUT_DIR.mkdir(exist_ok=True)

        try:
            self.engine.start()
        except Exception as e:
            self.log.critical(f"Browser failed to start: {e}")
            self.data.add_error(str(e))
            return self.data

        try:
            # ── LOGIN ────────────────────────────────────────────────────
            if not self.auth.login(self.username, self.password):
                self.data.add_error("Login failed")
                return self.data

            # ── DASHBOARD ────────────────────────────────────────────────
            self.log.info("Scraping dashboard...")
            dash_html = self._try_endpoints("dashboard")
            if dash_html:
                self._update_ids(dash_html)

            # ── PROFILE ──────────────────────────────────────────────────
            self.log.info("Scraping profile...")
            profile_html = self._try_endpoints("profile")
            if profile_html:
                self._update_ids(profile_html)
                self.data.profile = self.parser.parse_profile(profile_html)
                self.data.profile.student_id = self.username
                self.data.profile.batch_id = self._batch_id
                self.log.success(f"Profile: {self.data.profile.display_name}")

            # ── ATTENDANCE DATE VIEW ──────────────────────────────────────
            self.log.info("Scraping attendance...")
            att_html = self._try_endpoints("attendance_date")
            if att_html:
                self._update_ids(att_html)
                records, month_pct, overall_pct = self.parser.parse_attendance_page(att_html)
                self.data.attendance_records.extend(records)
                self.log.info(f"Date view: {len(records)} records | Month: {month_pct} | Overall: {overall_pct}")

            # ── ATTENDANCE SUBJECT VIEW ───────────────────────────────────
            if self._batch_id:
                subj_html = self._try_endpoints("attendance_subject")
                if subj_html:
                    subject_data = self.parser.parse_subject_summary(subj_html)
                    self.data.subject_attendance.update(subject_data)
                    self.log.success(f"Subject summary: {len(subject_data)} subjects")

                month_html = self._try_endpoints("attendance_month")
                if month_html:
                    month_records, _, _ = self.parser.parse_attendance_page(month_html)
                    self.data.attendance_records.extend(month_records)

            # ── CHECK INTERCEPTED APIs ────────────────────────────────────
            self._check_api_intercepts()

            # ── RESULTS ──────────────────────────────────────────────────
            self.log.info("Scraping results...")
            res_html = self._try_endpoints("results")
            if res_html:
                self.data.results = self.parser.parse_results(res_html)
                self.log.success(f"Results: {len(self.data.results)} entries")

            # ── TIMETABLE ────────────────────────────────────────────────
            self.log.info("Scraping timetable...")
            tt_html = self._try_endpoints("timetable")
            if tt_html:
                self.data.timetable = self.parser.parse_timetable(tt_html)
                self.log.success(f"Timetable: {len(self.data.timetable)} slots")

            # ── CONSOLIDATE ──────────────────────────────────────────────
            self._consolidate_attendance()

        except KeyboardInterrupt:
            self.log.warn("Interrupted by user.")
        except Exception as e:
            self.log.error(f"Unexpected error: {e}")
            self.log.debug(traceback.format_exc())
            self.data.add_error(str(e))
        finally:
            self.engine.stop()

        return self.data

    def _consolidate_attendance(self):
        """
        Build SubjectAttendance from raw records using a priority queue + hashmap.
        Deduplicates by (subject, date) — best-status wins.
        Time: O(n log n), Space: O(n)
        """
        STATUS_PRIORITY = {
            AttendanceStatus.PRESENT:    4,
            AttendanceStatus.DUTY_LEAVE: 3,
            AttendanceStatus.MEDICAL:    2,
            AttendanceStatus.ABSENT:     1,
            AttendanceStatus.UNKNOWN:    0,
        }

        # subject → date → best_status
        subject_day: Dict[str, Dict[str, AttendanceStatus]] = defaultdict(dict)
        subject_codes: Dict[str, str] = {}
        subject_topics: Dict[str, List[str]] = defaultdict(list)
        # Track per-subject streaks using ring buffers
        subject_rings: Dict[str, RingBuffer] = {}

        for rec in self.data.attendance_records:
            key = rec.subject_name or rec.subject_code
            if not key:
                continue

            subject_codes[key] = rec.subject_code

            curr = subject_day[key].get(rec.date)
            curr_p = STATUS_PRIORITY.get(curr, 0)
            new_p  = STATUS_PRIORITY.get(rec.status, 0)
            if new_p > curr_p:
                subject_day[key][rec.date] = rec.status

            if rec.topic and rec.topic not in subject_topics[key]:
                subject_topics[key].append(rec.topic)

        # Build/merge SubjectAttendance objects
        for subject_name, day_map in subject_day.items():
            if subject_name not in self.data.subject_attendance:
                self.data.subject_attendance[subject_name] = SubjectAttendance(
                    code=subject_codes.get(subject_name, ""),
                    name=subject_name,
                )

            sa = self.data.subject_attendance[subject_name]
            sa.code = subject_codes.get(subject_name, sa.code)
            sa.topics = subject_topics[subject_name]

            ring = RingBuffer(30)

            # Sort dates chronologically
            sorted_dates = sorted(day_map.keys(), key=lambda d: re.sub(r'\D', '', d))
            for date_str in sorted_dates:
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

            subject_rings[subject_name] = ring

        if self.data.subject_attendance:
            total = sum(sa.total_classes for sa in self.data.subject_attendance.values())
            self.log.success(f"Consolidated: {len(self.data.subject_attendance)} subjects, {total} total classes")
        else:
            self.log.warn("No attendance data could be parsed. Saved debug HTML files in etlab_output/ — please inspect them.")


# ─────────────────────────────────────────────────────────────────────────────
# ANALYTICS ENGINE
# ─────────────────────────────────────────────────────────────────────────────

class EtLabAnalytics:
    """
    Advanced analytics engine.
    Uses priority queues, statistical analysis, what-if simulation.
    """

    def __init__(self, data: AcademicData):
        self.data = data
        self._risk_heap = MinHeap()
        self._subject_trie = Trie()
        self._df_subjects: Optional[Any] = None
        self._df_records: Optional[Any] = None
        self._build_structures()

    def _build_structures(self):
        """Build all data structures from AcademicData."""
        for name, sa in self.data.subject_attendance.items():
            self._subject_trie.insert(name)
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
                "code": sa.code,
                "name": name,
                "short": self._short(name),
                "total": sa.total_classes,
                "present": sa.present,
                "absent": sa.absent,
                "duty": sa.duty_leave,
                "medical": sa.medical_leave,
                "pct": sa.percentage,
                "raw_pct": sa.raw_percentage,
                "safe": sa.is_safe,
                "danger": sa.is_danger,
                "can_bunk": sa.classes_can_bunk,
                "need_attend": sa.classes_to_attend,
                "shortage": sa.shortage,
                "vibe": sa.vibe_check,
            })
        df = pd.DataFrame(rows)
        return df.sort_values("pct")

    def _build_records_df(self):
        if not self.data.attendance_records:
            return pd.DataFrame()
        rows = [r.to_dict() for r in self.data.attendance_records]
        return pd.DataFrame(rows)

    @staticmethod
    def _short(name: str, n: int = 28) -> str:
        words = name.split()
        s = " ".join(words[:3])
        return (s[:n] + "…") if len(s) > n else s

    def summary(self) -> Dict[str, Any]:
        """Compute overall summary stats."""
        subjects = list(self.data.subject_attendance.values())
        if not subjects:
            return {}

        total_present  = sum(s.present for s in subjects)
        total_classes  = sum(s.total_classes for s in subjects)
        total_absent   = sum(s.absent for s in subjects)
        overall_pct    = round(total_present / total_classes * 100, 2) if total_classes else 0
        safe_subjects  = [s for s in subjects if s.is_safe]
        risky_subjects = [s for s in subjects if not s.is_safe]

        # Best/worst by heap
        risk_sorted = self._risk_heap.to_sorted_list()
        worst = risk_sorted[0][1] if risk_sorted else None
        best  = risk_sorted[-1][1] if risk_sorted else None

        # GPA estimate from results
        cgpa = self._compute_cgpa()

        return {
            "total_subjects":       len(subjects),
            "total_classes":        total_classes,
            "total_present":        total_present,
            "total_absent":         total_absent,
            "overall_pct":          overall_pct,
            "safe_count":           len(safe_subjects),
            "risky_count":          len(risky_subjects),
            "danger_count":         sum(1 for s in subjects if s.is_danger),
            "total_can_bunk":       sum(s.classes_can_bunk for s in safe_subjects),
            "total_need_attend":    sum(s.classes_to_attend for s in risky_subjects),
            "worst_subject":        worst.name if worst else "N/A",
            "worst_pct":            worst.percentage if worst else 0,
            "best_subject":         best.name if best else "N/A",
            "best_pct":             best.percentage if best else 0,
            "cgpa_estimate":        cgpa,
            "overall_vibe":         self._overall_vibe(overall_pct),
        }

    def _compute_cgpa(self) -> float:
        """Estimate CGPA from results."""
        if not self.data.results:
            return 0.0
        total_gp = total_cr = 0
        for r in self.data.results:
            gp = r.grade_points
            try:
                cr = float(r.credits) if r.credits else 0
            except ValueError:
                cr = 0
            total_gp += gp * cr
            total_cr += cr
        return round(total_gp / total_cr, 2) if total_cr > 0 else 0.0

    @staticmethod
    def _overall_vibe(pct: float) -> str:
        if pct >= 90:   return "you absolute nerd, never missed a class 🏆"
        if pct >= 80:   return "solid attendance, no stress bestie ✨"
        if pct >= 75:   return "technically safe but don't push it 😬"
        if pct >= 65:   return "bruh you're on thin ice fr ⚠️"
        if pct >= 50:   return "BSOD (bro seriously on destruction) 💀"
        return              "detention% speedrun world record 🚨"

    def what_if(self, subject_name: str, attend_n: int, total_n: int) -> Dict[str, Any]:
        """
        What-if simulator:
        If I attend `attend_n` out of the next `total_n` classes,
        what will my attendance be?
        """
        # Fuzzy find subject
        matches = self._subject_trie.fuzzy_find(subject_name)
        if not matches:
            return {"error": "Subject not found"}

        _, best_match = matches[0]
        sa = self.data.subject_attendance.get(best_match)
        if not sa:
            return {"error": f"No data for {best_match}"}

        new_pct = sa.predict_after_n_classes(total_n, attend_n)
        return {
            "subject": best_match,
            "current_pct": sa.percentage,
            "new_pct": new_pct,
            "change": round(new_pct - sa.percentage, 2),
            "still_safe": new_pct >= SAFE_THRESHOLD,
            "message": f"If you attend {attend_n}/{total_n} classes, you'll be at {new_pct}% " +
                       ("✅ safe!" if new_pct >= SAFE_THRESHOLD else "❌ still at risk"),
        }

    def bunk_planner(self, days_remaining: int, classes_per_day: int = 4) -> Dict[str, Any]:
        """
        Given remaining classes, plan optimal attendance strategy.
        Uses a greedy algorithm: prioritize at-risk subjects.
        """
        total_remaining = days_remaining * classes_per_day
        plan = {}

        # Sort by urgency (shortage first)
        sorted_subjects = sorted(
            self.data.subject_attendance.values(),
            key=lambda s: (-s.shortage, s.percentage)
        )

        for sa in sorted_subjects:
            if sa.is_safe:
                plan[sa.name] = {
                    "status": "safe",
                    "can_miss": sa.classes_can_bunk,
                    "advice": f"can miss up to {sa.classes_can_bunk} more, enjoy life 🎉"
                }
            else:
                weeks = sa.weeks_until_safe()
                plan[sa.name] = {
                    "status": "at_risk",
                    "need_attend": sa.classes_to_attend,
                    "advice": f"attend next {sa.classes_to_attend} consecutively (~{weeks} weeks)",
                    "weeks_to_safe": weeks,
                }

        return {
            "days_remaining": days_remaining,
            "total_remaining_classes": total_remaining,
            "plan": plan,
        }

    def absence_heatmap_data(self) -> Dict[str, List[str]]:
        """Return dates of absence per subject for heatmap."""
        return {
            name: sa.dates_absent
            for name, sa in self.data.subject_attendance.items()
        }

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
    """Gen-Z friendly terminal dashboard. No corporate vibes."""

    def __init__(self, data: AcademicData, analytics: EtLabAnalytics):
        self.data = data
        self.analytics = analytics

    def show_all(self):
        self.show_banner()
        self.show_profile()
        self.show_attendance_table()
        self.show_summary()
        if self.data.results:
            self.show_results()
        if self.data.errors:
            self.show_errors()

    def show_banner(self):
        lines = [
            C.bold(C.magenta("  ┌─────────────────────────────────────────┐")),
            C.bold(C.magenta("  │       ETLAB PRO — YOUR ATTENDANCE PLUG  │")),
            C.bold(C.magenta("  │   'know before you yolo the bunk' 🎓    │")),
            C.bold(C.magenta("  └─────────────────────────────────────────┘")),
            C.dim(f"  Scraped at: {self.data.scraped_at[:19]}"),
        ]
        print("\n" + "\n".join(lines) + "\n")

    def show_profile(self):
        p = self.data.profile
        lines = [
            f"  👤  {C.bold(p.display_name)}",
            f"  🎓  {p.department or 'N/A'}  |  Sem {p.semester or 'N/A'}",
            f"  🏫  {p.college or 'N/A'}",
            f"  🔑  {p.student_id}  |  Roll: {p.roll_number or 'N/A'}",
        ]
        print(_box(lines, title="STUDENT PROFILE", color=C.BCYAN))
        print()

    def show_attendance_table(self):
        subjects = self.data.subject_attendance
        if not subjects:
            print(C.yellow("  ⚠️  No attendance data found. Check debug HTML files."))
            return

        print(C.bold(C.cyan("\n  📊 ATTENDANCE BREAKDOWN\n")))

        headers = ["Subject", "Code", "Tot", "✅Pre", "❌Abs", "🟡Dty", "%", "Bar", "Status", "Bunk💤", "Need📚"]
        rows = []

        sorted_subjects = sorted(subjects.values(), key=lambda s: s.percentage)
        for sa in sorted_subjects:
            pct = sa.percentage
            pct_str = (C.green if sa.is_safe else C.red)(f"{pct:.1f}%")
            bar = _progress_bar(pct, width=12, show_pct=False)
            status = (C.green("✅ SAFE") if sa.is_safe else
                      (C.red("💀 DEAD") if sa.is_danger else C.yellow("⚠️ RISKY")))
            bunk = C.green(str(sa.classes_can_bunk)) if sa.is_safe else C.dim("-")
            need = C.red(str(sa.classes_to_attend)) if not sa.is_safe else C.dim("-")
            name_short = sa.name[:28] + "…" if len(sa.name) > 28 else sa.name

            rows.append([
                name_short,
                sa.code or "-",
                str(sa.total_classes),
                str(sa.present),
                str(sa.absent),
                str(sa.duty_leave),
                pct_str,
                bar,
                status,
                bunk,
                need,
            ])

        print(_table(headers, rows))
        print()

    def show_summary(self):
        s = self.analytics.summary()
        if not s:
            return

        pct = s["overall_pct"]
        pct_color = C.green if pct >= 75 else C.red

        lines = [
            f"  🎯  Overall Attendance: {pct_color(f'{pct}%')}   {_progress_bar(pct, width=20)}",
            f"  📚  Total Classes: {s['total_classes']}  ({C.green(str(s['total_present']) + ' present')} / {C.red(str(s['total_absent']) + ' absent')})",
            f"  ✅  Safe Subjects: {C.green(str(s['safe_count']))}   ⚠️  At Risk: {C.yellow(str(s['risky_count']))}   💀 Danger: {C.red(str(s['danger_count']))}",
            f"  💤  Total Bunk Budget: {C.green(str(s['total_can_bunk']))} classes across all safe subjects",
            f"  📖  Classes to Grind: {C.red(str(s['total_need_attend']))} classes needed across at-risk subjects",
            f"  🏆  Best: {C.green(s['best_subject'][:35])} ({s['best_pct']}%)",
            f"  💀  Worst: {C.red(s['worst_subject'][:35])} ({s['worst_pct']}%)",
        ]
        if s["cgpa_estimate"] > 0:
            lines.append(f"  📈  Estimated CGPA: {C.cyan(str(s['cgpa_estimate']))}")

        lines.append(f"\n  🔥  Vibe Check: {C.magenta(s['overall_vibe'])}")

        print(_box(lines, title="ACADEMIC SUMMARY", color=C.BMAGENTA))
        print()

        # Per-subject vibe
        print(C.bold(C.cyan("  💬 Subject Vibes:\n")))
        for name, sa in sorted(self.data.subject_attendance.items(), key=lambda x: x[1].percentage):
            emoji = sa.status_emoji
            print(f"  {emoji}  {C.bold(name[:35])} — {C.dim(sa.vibe_check)}")
        print()

    def show_results(self):
        print(C.bold(C.cyan("\n  📝 EXAM RESULTS\n")))
        headers = ["Subject", "Code", "Grade", "Marks", "Credits", "Result"]
        rows = []
        for r in self.data.results:
            result_str = C.green("PASS") if r.is_pass else (C.red("FAIL") if r.result else "-")
            rows.append([
                r.subject_name[:35], r.subject_code,
                C.yellow(r.grade), f"{r.marks_obtained}/{r.max_marks}" if r.max_marks else r.marks_obtained,
                r.credits, result_str,
            ])
        print(_table(headers, rows))
        print()

    def show_errors(self):
        if not self.data.errors:
            return
        print(C.yellow("\n  ⚠️  Errors during scraping:"))
        for err in self.data.errors:
            print(C.dim(f"    {err}"))
        print()

    def interactive_what_if(self):
        """Interactive what-if attendance simulator."""
        subjects = list(self.data.subject_attendance.keys())
        if not subjects:
            return

        print(C.bold(C.cyan("\n  🔮 WHAT-IF SIMULATOR\n")))
        print("  Which subject? (type name or partial match)")
        for i, name in enumerate(subjects[:10]):
            print(f"  {C.dim(str(i+1) + '.')} {name[:45]}")

        try:
            choice = input(C.cyan("\n  > ")).strip()
            attend = int(input(C.cyan("  Classes you'll attend: ")).strip())
            total  = int(input(C.cyan("  Out of how many total classes: ")).strip())

            result = self.analytics.what_if(choice, attend, total)
            if "error" in result:
                print(C.red(f"  {result['error']}"))
            else:
                change_str = (C.green(f"+{result['change']}%") if result['change'] >= 0
                              else C.red(f"{result['change']}%"))
                print(_box([
                    f"  Subject: {C.bold(result['subject'][:40])}",
                    f"  Current: {C.cyan(str(result['current_pct']) + '%')}",
                    f"  After:   {C.green(str(result['new_pct']) + '%')} ({change_str})",
                    f"  {result['message']}",
                ], title="WHAT-IF RESULT", color=C.BBLUE))
        except (ValueError, KeyboardInterrupt):
            print(C.dim("  Skipped."))


# ─────────────────────────────────────────────────────────────────────────────
# VISUALIZER
# ─────────────────────────────────────────────────────────────────────────────

class EtLabVisualizer:
    """
    Matplotlib + Seaborn chart suite.
    Dark theme, color-coded by risk level.
    """

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
        self.data = analytics.data
        self._apply_theme()

    def _apply_theme(self):
        if not MATPLOTLIB_OK:
            return
        p = self.PALETTE
        plt.style.use("dark_background")
        plt.rcParams.update({
            "figure.facecolor":  p["bg"],
            "axes.facecolor":    p["surface"],
            "axes.edgecolor":    p["grid"],
            "axes.labelcolor":   p["text"],
            "xtick.color":       p["text"],
            "ytick.color":       p["text"],
            "text.color":        p["text"],
            "grid.color":        p["grid"],
            "grid.alpha":        0.5,
            "font.family":       "monospace",
            "figure.autolayout": False,
        })

    def _bar_colors(self, values: List[float]) -> List[str]:
        p = self.PALETTE
        return [p["safe"] if v >= 75 else (p["danger"] if v < 60 else p["warning"]) for v in values]

    def plot_all(self):
        if not MATPLOTLIB_OK:
            print(C.yellow("  matplotlib not available — skipping charts"))
            return
        if not self.data.subject_attendance:
            return

        print(C.dim("  Generating charts..."))
        try:
            self._plot_attendance_dashboard()
            self._plot_bunk_budget()
            self._plot_trend() if PANDAS_OK and not self.analytics.df_records.empty else None
            print(C.green(f"  Charts saved to {OUTPUT_DIR}/"))
        except Exception as e:
            print(C.yellow(f"  Chart error: {e}"))

    def _plot_attendance_dashboard(self):
        """Main dashboard: bar chart + pie + stats."""
        df = self.analytics.df_subjects
        if df is None or df.empty:
            return

        fig = plt.figure(figsize=(18, 10), facecolor=self.PALETTE["bg"])
        gs = gridspec.GridSpec(2, 3, figure=fig, hspace=0.4, wspace=0.35)

        # ── Main bar chart ────────────────────────────────────────────────
        ax1 = fig.add_subplot(gs[0, :2])
        colors = self._bar_colors(df["pct"].tolist())
        bars = ax1.barh(df["short"], df["pct"], color=colors,
                        edgecolor=self.PALETTE["grid"], height=0.65, linewidth=0.5)
        ax1.axvline(x=75, color=self.PALETTE["warning"], linestyle="--", linewidth=1.5,
                    label="75% threshold", alpha=0.8)
        ax1.axvline(x=60, color=self.PALETTE["danger"], linestyle=":", linewidth=1,
                    label="60% danger zone", alpha=0.6)

        for bar, pct in zip(bars, df["pct"]):
            ax1.text(min(bar.get_width() + 0.8, 108), bar.get_y() + bar.get_height() / 2,
                     f"{pct:.1f}%", va="center", ha="left", fontsize=8.5,
                     color=self.PALETTE["text"], fontweight="bold")

        ax1.set_xlim(0, 112)
        ax1.set_xlabel("Attendance %", fontsize=10)
        ax1.set_title("Subject-wise Attendance", fontsize=13, fontweight="bold",
                      color=self.PALETTE["text"], pad=10)
        ax1.legend(loc="lower right", fontsize=8, framealpha=0.3)
        ax1.set_facecolor(self.PALETTE["surface"])

        # ── Pie chart ─────────────────────────────────────────────────────
        ax2 = fig.add_subplot(gs[0, 2])
        subjects = list(self.data.subject_attendance.values())
        tp = sum(s.present for s in subjects)
        ta = sum(s.absent for s in subjects)
        td = sum(s.duty_leave for s in subjects)
        tm = sum(s.medical_leave for s in subjects)

        pie_vals   = [v for v in [tp, ta, td, tm] if v > 0]
        pie_labels = [l for v, l in zip([tp, ta, td, tm],
                      ["Present", "Absent", "Duty", "Medical"]) if v > 0]
        pie_colors = [self.PALETTE[c] for c, v in zip(
                      ["safe","danger","warning","accent"], [tp, ta, td, tm]) if v > 0]

        if pie_vals:
            wedges, _, autotexts = ax2.pie(
                pie_vals, labels=pie_labels, colors=pie_colors,
                autopct="%1.0f%%", startangle=90,
                wedgeprops={"edgecolor": self.PALETTE["bg"], "linewidth": 2},
                textprops={"color": self.PALETTE["text"], "fontsize": 8},
            )
            for at in autotexts:
                at.set_color(self.PALETTE["bg"])
                at.set_fontweight("bold")

        total_all = sum(pie_vals) if pie_vals else 1
        overall = round(tp / total_all * 100, 1)
        ax2.set_title(f"Overall: {overall}%", fontsize=12, fontweight="bold",
                      color=self.PALETTE["text"])
        ax2.set_facecolor(self.PALETTE["surface"])

        # ── Stacked present/absent ────────────────────────────────────────
        ax3 = fig.add_subplot(gs[1, :2])
        x = range(len(df))
        ax3.bar(x, df["present"], label="Present ✅", color=self.PALETTE["safe"],
                edgecolor=self.PALETTE["bg"], linewidth=0.5)
        ax3.bar(x, df["absent"], bottom=df["present"], label="Absent ❌",
                color=self.PALETTE["danger"], edgecolor=self.PALETTE["bg"], linewidth=0.5)
        ax3.bar(x, df["duty"], bottom=df["present"] + df["absent"], label="Duty 🟡",
                color=self.PALETTE["warning"], edgecolor=self.PALETTE["bg"], linewidth=0.5)
        ax3.set_xticks(list(x))
        ax3.set_xticklabels(df["short"], rotation=30, ha="right", fontsize=8)
        ax3.set_ylabel("Classes")
        ax3.set_title("Present vs Absent vs Duty", fontsize=11, fontweight="bold",
                      color=self.PALETTE["text"])
        ax3.legend(fontsize=8, framealpha=0.3)
        ax3.set_facecolor(self.PALETTE["surface"])

        # ── Stats summary box ─────────────────────────────────────────────
        ax4 = fig.add_subplot(gs[1, 2])
        ax4.axis("off")
        s = self.analytics.summary()
        summary_text = (
            f"BUNK BUDGET 💤\n\n"
            f"Total classes you\ncan still skip:\n\n"
            f"  {s.get('total_can_bunk', 0):>4} classes\n\n"
            f"GRIND REQUIRED 📚\n\n"
            f"Classes needed to\nget everyone safe:\n\n"
            f"  {s.get('total_need_attend', 0):>4} classes\n\n"
            f"Subjects safe: {s.get('safe_count',0)}\n"
            f"At risk:       {s.get('risky_count',0)}\n"
            f"Danger zone:   {s.get('danger_count',0)}"
        )
        ax4.text(0.05, 0.95, summary_text, transform=ax4.transAxes,
                 va="top", ha="left", fontsize=10, fontfamily="monospace",
                 color=self.PALETTE["text"],
                 bbox=dict(boxstyle="round,pad=0.5", facecolor=self.PALETTE["surface"],
                           edgecolor=self.PALETTE["accent"], linewidth=1.5))

        plt.suptitle(
            f"📊 {self.data.profile.display_name} — Attendance Report",
            fontsize=14, fontweight="bold", color=self.PALETTE["text"], y=1.01
        )

        path = OUTPUT_DIR / "attendance_dashboard.png"
        plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
        plt.close()

    def _plot_bunk_budget(self):
        """Bunk budget bar chart."""
        df = self.analytics.df_subjects
        if df is None or df.empty:
            return

        fig, ax = plt.subplots(figsize=(14, 5), facecolor=self.PALETTE["bg"])
        ax.set_facecolor(self.PALETTE["surface"])

        colors = [self.PALETTE["safe"] if v > 0 else self.PALETTE["danger"]
                  for v in df["can_bunk"]]
        ax.bar(df["short"], df["can_bunk"], color=colors,
               edgecolor=self.PALETTE["bg"], linewidth=0.5)
        ax.axhline(0, color=self.PALETTE["text"], linewidth=0.8)

        for i, (val, shortage) in enumerate(zip(df["can_bunk"], df["shortage"])):
            if val == 0 and shortage > 0:
                ax.text(i, -0.3, f"-{shortage}", ha="center", va="top",
                        fontsize=8, color=self.PALETTE["danger"], fontweight="bold")

        ax.set_title("Bunk Budget  💤  (green = can skip, red = already short)",
                     fontsize=12, fontweight="bold", color=self.PALETTE["text"])
        ax.set_ylabel("Classes can skip / short")
        plt.xticks(rotation=30, ha="right", fontsize=8)
        plt.tight_layout()

        path = OUTPUT_DIR / "bunk_budget.png"
        plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
        plt.close()

    def _plot_trend(self):
        """Attendance trend over time (if record-level data available)."""
        df = self.analytics.df_records
        if df is None or df.empty or "date" not in df.columns:
            return

        try:
            df["date_parsed"] = pd.to_datetime(df["date"], dayfirst=True, errors="coerce")
            df = df.dropna(subset=["date_parsed"])
            if df.empty:
                return

            daily = df.groupby("date_parsed").apply(
                lambda g: (g["status"] == AttendanceStatus.PRESENT.value).mean() * 100
            ).reset_index()
            daily.columns = ["date", "pct"]
            daily = daily.sort_values("date")

            if len(daily) < 3:
                return

            fig, ax = plt.subplots(figsize=(14, 4), facecolor=self.PALETTE["bg"])
            ax.set_facecolor(self.PALETTE["surface"])

            ax.fill_between(daily["date"], daily["pct"], alpha=0.3, color=self.PALETTE["accent"])
            ax.plot(daily["date"], daily["pct"], color=self.PALETTE["accent"],
                    linewidth=2, marker="o", markersize=3)
            ax.axhline(75, color=self.PALETTE["warning"], linestyle="--",
                       linewidth=1.5, label="75% threshold")

            # Trend line
            if SCIPY_OK and len(daily) > 5:
                x_num = (daily["date"] - daily["date"].min()).dt.days.values
                slope, intercept, *_ = scipy_stats.linregress(x_num, daily["pct"].values)
                trend_y = slope * x_num + intercept
                ax.plot(daily["date"], trend_y, color=self.PALETTE["danger"],
                        linestyle=":", linewidth=1.5, label=f"Trend ({slope:+.2f}%/day)")

            ax.set_title("Attendance Trend Over Time", fontsize=12,
                         fontweight="bold", color=self.PALETTE["text"])
            ax.set_ylabel("Daily Attendance %")
            ax.legend(fontsize=8, framealpha=0.3)
            plt.xticks(rotation=30, ha="right", fontsize=8)
            plt.tight_layout()

            path = OUTPUT_DIR / "attendance_trend.png"
            plt.savefig(path, dpi=150, bbox_inches="tight", facecolor=self.PALETTE["bg"])
            plt.close()
        except Exception as e:
            pass  # trend plot is optional


# ─────────────────────────────────────────────────────────────────────────────
# EXPORTER
# ─────────────────────────────────────────────────────────────────────────────

class EtLabExporter:
    """Export to JSON, CSV, and a markdown report."""

    def __init__(self, data: AcademicData, analytics: EtLabAnalytics):
        self.data = data
        self.analytics = analytics

    def export_all(self):
        self._export_json()
        self._export_csv()
        self._export_markdown()

    def _export_json(self):
        path = OUTPUT_DIR / "academic_data.json"
        payload = {
            "scraped_at": self.data.scraped_at,
            "profile": asdict(self.data.profile),
            "summary": self.analytics.summary(),
            "subjects": {name: sa.to_dict() for name, sa in self.data.subject_attendance.items()},
            "results": [asdict(r) for r in self.data.results],
            "timetable": [asdict(t) for t in self.data.timetable],
            "errors": self.data.errors,
        }
        path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
        print(C.green(f"  📁 JSON: {path}"))

    def _export_csv(self):
        if PANDAS_OK and self.analytics.df_subjects is not None and not self.analytics.df_subjects.empty:
            p = OUTPUT_DIR / "attendance_summary.csv"
            self.analytics.df_subjects.to_csv(p, index=False)
            print(C.green(f"  📁 CSV:  {p}"))

        if PANDAS_OK and self.analytics.df_records is not None and not self.analytics.df_records.empty:
            p2 = OUTPUT_DIR / "attendance_records.csv"
            self.analytics.df_records.to_csv(p2, index=False)
            print(C.green(f"  📁 CSV:  {p2}"))

    def _export_markdown(self):
        """Generate a nice markdown report."""
        path = OUTPUT_DIR / "attendance_report.md"
        s = self.analytics.summary()
        p = self.data.profile

        lines = [
            f"# 🎓 Attendance Report — {p.display_name}",
            f"**Generated:** {self.data.scraped_at[:19]}  ",
            f"**Department:** {p.department}  |  **Semester:** {p.semester}",
            "",
            "## 📊 Summary",
            f"| Metric | Value |",
            f"|--------|-------|",
            f"| Overall Attendance | **{s.get('overall_pct', 0)}%** |",
            f"| Total Classes | {s.get('total_classes', 0)} |",
            f"| Present | {s.get('total_present', 0)} |",
            f"| Absent | {s.get('total_absent', 0)} |",
            f"| Safe Subjects | {s.get('safe_count', 0)} |",
            f"| At Risk | {s.get('risky_count', 0)} |",
            f"| Total Bunk Budget | **{s.get('total_can_bunk', 0)} classes** |",
            "",
            "## 📋 Subject-wise",
            "| Subject | Code | % | Status | Bunk Left | Need Attend |",
            "|---------|------|---|--------|-----------|-------------|",
        ]

        for name, sa in sorted(self.data.subject_attendance.items(), key=lambda x: x[1].percentage):
            status = "✅ Safe" if sa.is_safe else ("💀 Danger" if sa.is_danger else "⚠️ Risk")
            bunk = str(sa.classes_can_bunk) if sa.is_safe else "-"
            need = str(sa.classes_to_attend) if not sa.is_safe else "-"
            lines.append(f"| {name[:40]} | {sa.code} | {sa.percentage}% | {status} | {bunk} | {need} |")

        lines += ["", "---", "*Generated by EtLab Pro — your attendance bestie 🎓*"]
        path.write_text("\n".join(lines), encoding="utf-8")
        print(C.green(f"  📁 MD:   {path}"))


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="EtLab Pro — Your Attendance Bestie 🎓",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""
        Examples:
          python etlab_scraper.py -u 925059 -p 6a014a
          python etlab_scraper.py -u 925059 -p 6a014a --show-browser
          python etlab_scraper.py -u 925059 -p 6a014a --no-charts --no-export
          python etlab_scraper.py -u 925059 -p 6a014a --what-if
        """),
    )
    p.add_argument("-u", "--username", required=True,      help="EtLab student ID / username")
    p.add_argument("-p", "--password", required=True,      help="EtLab password")
    p.add_argument("--show-browser",  action="store_true", help="Show browser window (debug)")
    p.add_argument("--no-cache",      action="store_true", help="Clear and ignore cached pages")
    p.add_argument("--no-charts",     action="store_true", help="Skip chart generation")
    p.add_argument("--no-export",     action="store_true", help="Skip JSON/CSV/MD export")
    p.add_argument("--what-if",       action="store_true", help="Run interactive what-if simulator")
    p.add_argument("--debug",         action="store_true", help="Enable debug logging")
    p.add_argument("-o", "--output",  default="etlab_output", help="Output directory")
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
        log.critical("Playwright is required. Install with:")
        log.critical("  pip install playwright")
        log.critical("  playwright install chromium")
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
        log=log,
    )
    data = scraper.scrape_all()

    # ── ANALYTICS ─────────────────────────────────────────────────────────
    analytics = EtLabAnalytics(data)

    # ── DISPLAY ───────────────────────────────────────────────────────────
    display = EtLabDisplay(data, analytics)
    display.show_all()

    # ── WHAT-IF ───────────────────────────────────────────────────────────
    if args.what_if and data.subject_attendance:
        display.interactive_what_if()

    # ── CHARTS ────────────────────────────────────────────────────────────
    if not args.no_charts:
        viz = EtLabVisualizer(analytics)
        viz.plot_all()

    # ── EXPORT ────────────────────────────────────────────────────────────
    if not args.no_export:
        print(C.bold(C.cyan("\n  📦 Exporting data...\n")))
        exporter = EtLabExporter(data, analytics)
        exporter.export_all()

    # ── FINAL STATUS ──────────────────────────────────────────────────────
    s = analytics.summary()
    if s:
        pct = s["overall_pct"]
        msg = C.green("You're doing great, keep it up! ✨") if pct >= 75 else \
              C.red("Bro please start attending 💀")
        print(f"\n  {msg}")
    else:
        print(C.yellow("\n  ⚠️  No attendance data found."))
        print(C.dim("  Saved debug HTML files in etlab_output/ — open them in Chrome"))
        print(C.dim("  to see what the server is actually returning."))
        print(C.dim("  Also check etlab_output/debug_login.png for login screenshot."))

    print(C.dim(f"\n  Log: {LOG_FILE}"))
    print(C.dim(f"  Output: {OUTPUT_DIR}/\n"))


if __name__ == "__main__":
    main()
