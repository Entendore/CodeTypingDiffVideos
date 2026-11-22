#!/usr/bin/env python3
"""
Junior vs Senior Dev — Code Typing Studio (Expert Edition + Batch Processing)
=============================================================================

Added batch features:
  • File table with checkboxes (replaces tree view)
  • Batch export queue with per-file status tracking
  • Recursive folder scanning with depth control
  • Select All / Deselect All with Shift+click range selection
  • Drag & drop file support
  • Output naming template ({name}, {date}, {lang}, {wpm})
  • Auto-thumbnail generation (4 JPG candidates)
  • YouTube chapters & description generation
  • Disk space checking before export
  • Open Output folder / Play Last buttons
  • Context menu: "Export This File Only"

Audio/ASMR Features:
  • Professional per-key sound design (row-based pitch shifting)
  • Anti-aliased pitch shifting for highs, sub-bass boost for lows
  • Two-stage ASMR mastering (de-essing, air band, sub-warmth)
  • Sidechain ducked BGM mixing
  • 19 distinct sound presets (Mechanical, ASMR, Organic, etc.)

Requirements:
    pip install PySide6 numpy
    # FFmpeg must be on PATH for video export
"""
from __future__ import annotations

# ═══════════════════════════════════════════════════════════════════
# SECTION 0 — IMPORTS & COMPATIBILITY SHIMS
# ═══════════════════════════════════════════════════════════════════
import bisect
import io
import json
import logging
import math
import os
import platform
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time as _time
import wave
import faulthandler
from abc import ABC, abstractmethod
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor, Future
from contextlib import contextmanager, suppress
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from enum import Enum, auto
from functools import lru_cache, wraps
from pathlib import Path
from typing import (
    Any, Callable, Dict, Final, FrozenSet, Generator, Iterable,
    Iterator, List, Optional, Protocol, Sequence, Tuple, TypeVar, Union,
    runtime_checkable,
)

import numpy as np

from PySide6.QtCore import (
    QElapsedTimer, QEvent, QIODevice, QObject, QPoint, QPointF, QRect,
    QSize, Qt, QThread, QTimer, QUrl, Signal, Slot,
    QPropertyAnimation, QEasingCurve, QRegularExpression, QSettings,
    QStandardPaths, QModelIndex, QBuffer,
)
from PySide6.QtGui import (
    QBrush, QColor, QFont, QFontDatabase, QFontMetrics, QImage,
    QLinearGradient, QPainter, QPainterPath, QPalette, QPen, QPixmap,
    QPolygonF, QKeySequence, QShortcut, QSyntaxHighlighter, QTextCharFormat,
    QTextCursor, QTextFormat, QDragEnterEvent, QDropEvent,
)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtWidgets import (
    QApplication, QCheckBox, QComboBox, QDialog, QDialogButtonBox,
    QDoubleSpinBox, QFileDialog, QFormLayout, QFrame, QGraphicsDropShadowEffect,
    QGridLayout, QGroupBox, QHBoxLayout, QHeaderView, QLabel, QLineEdit,
    QMainWindow, QListView, QMenu, QMessageBox, QPlainTextEdit, QProgressBar,
    QPushButton, QRadioButton, QScrollArea, QSizePolicy, QSlider, QSpinBox,
    QSplitter, QStatusBar, QStyledItemDelegate,
    QStyle, QStyleFactory, QTabWidget, QTableWidget, QTableWidgetItem,
    QTreeView, QVBoxLayout, QWidget, QFileSystemModel, QProgressDialog,
    QTimeEdit,
)

faulthandler.enable()

# ═══════════════════════════════════════════════════════════════════
# SECTION 1 — EXCEPTION HIERARCHY & STRUCTURED LOGGING
# ═══════════════════════════════════════════════════════════════════

class StudioError(Exception):
    """Base exception for all studio errors."""

class ConfigurationError(StudioError):
    """Raised when configuration is invalid."""

class RenderingError(StudioError):
    """Raised during frame rendering."""

class AudioGenerationError(StudioError):
    """Raised during audio synthesis."""

class ExportError(StudioError):
    """Raised during video export."""

class FFmpegError(ExportError):
    """Raised when FFmpeg operations fail."""

class EncoderError(ExportError):
    """Raised when video encoding fails."""


class ContextualLogger(logging.LoggerAdapter):
    """Logger adapter that injects contextual fields into every record."""
    def process(self, msg: str, kwargs: dict) -> Tuple[str, dict]:
        ctx = self.extra or {}
        ctx_str = " ".join(f"{k}={v}" for k, v in ctx.items() if v is not None)
        return (f"[{ctx_str}] {msg}" if ctx_str else msg), kwargs


log = logging.getLogger("JuniorSeniorStudio")
log.setLevel(logging.DEBUG)
_fh = logging.FileHandler("studio.log", mode="w", encoding="utf-8")
_fh.setLevel(logging.DEBUG)
_fh.setFormatter(logging.Formatter(
    "%(asctime)s | %(levelname)-7s | %(threadName)-20s | %(message)s",
    datefmt="%H:%M:%S",
))
_sh = logging.StreamHandler()
_sh.setLevel(logging.WARNING)
_sh.setFormatter(logging.Formatter("%(levelname)-7s | %(message)s"))
log.addHandler(_fh)
log.addHandler(_sh)


def get_logger(name: str, **context) -> ContextualLogger:
    return ContextualLogger(log, {"ctx": name, **context})


# ═══════════════════════════════════════════════════════════════════
# SECTION 2 — DECORATORS
# ═══════════════════════════════════════════════════════════════════

T = TypeVar("T")


def timed(fn: Callable) -> Callable:
    @wraps(fn)
    def wrapper(*args, **kwargs):
        start = _time.perf_counter()
        try:
            return fn(*args, **kwargs)
        finally:
            elapsed = (_time.perf_counter() - start) * 1000
            log.debug("⏱ %s took %.2fms", fn.__qualname__, elapsed)
    return wrapper


def retry(max_attempts: int = 3, delay: float = 0.5,
          exceptions: tuple = (Exception,)):
    def decorator(fn: Callable) -> Callable:
        @wraps(fn)
        def wrapper(*args, **kwargs):
            last_exc = None
            for attempt in range(1, max_attempts + 1):
                try:
                    return fn(*args, **kwargs)
                except exceptions as e:
                    last_exc = e
                    log.warning("Attempt %d/%d failed: %s", attempt, max_attempts, e)
                    if attempt < max_attempts:
                        _time.sleep(delay * (2 ** (attempt - 1)))
            raise last_exc
        return wrapper
    return decorator


def thread_safe(lock: Optional[threading.Lock] = None):
    _lock = lock or threading.Lock()
    def decorator(fn: Callable) -> Callable:
        @wraps(fn)
        def wrapper(*args, **kwargs):
            with _lock:
                return fn(*args, **kwargs)
        return wrapper
    return decorator


# ═══════════════════════════════════════════════════════════════════
# SECTION 3 — ENUMS & IMMUTABLE CONSTANTS
# ═══════════════════════════════════════════════════════════════════

class KeyEventType(Enum):
    PRESS = auto()
    RELEASE = auto()
    BACKSPACE = auto()
    ENTER = auto()
    TAB = auto()
    SPACE = auto()


class PaneLayout(Enum):
    SIDE_BY_SIDE = "Side by Side (50/50)"
    STACKED = "Stacked (50/50)"
    JUNIOR_BIG = "Junior Big (70/30)"
    SENIOR_BIG = "Senior Big (70/30)"
    PIP_SENIOR_BIG = "PIP - Senior Big (Junior Small)"
    PIP_JUNIOR_BIG = "PIP - Junior Big (Senior Small)"

    @classmethod
    def from_str(cls, s: str) -> "PaneLayout":
        try:
            return cls(s)
        except ValueError:
            return cls.SIDE_BY_SIDE


class KeyboardPosition(Enum):
    BOTTOM_CENTER = "bottom_center"
    BOTTOM_RIGHT = "bottom_right"
    BOTTOM_LEFT = "bottom_left"
    TOP_CENTER = "top_center"
    TOP_RIGHT = "top_right"
    TOP_LEFT = "top_left"
    CENTER_LEFT = "center_left"
    CENTER_RIGHT = "center_right"


class ExportFormat(Enum):
    YOUTUBE_16_9 = "YouTube (16:9)"
    YOUTUBE_SHORTS_9_16 = "YouTube Shorts (9:16)"


class QualityPreset(Enum):
    DRAFT = "Draft (720p, 30fps)"
    MEDIUM = "Medium (1080p, 30fps)"
    HIGH = "High (1080p, 60fps)"
    ULTRA = "Ultra (4K, 60fps)"


CWD: Final[Path] = Path.cwd()
INPUT_DIR: Final[Path] = CWD / "input"
OUTPUT_DIR: Final[Path] = CWD / "output"
TEMP_DIR: Final[Path] = CWD / "temp"
SETTINGS_FILE: Final[Path] = CWD / "settings.json"

for _d in (INPUT_DIR, OUTPUT_DIR, TEMP_DIR):
    _d.mkdir(parents=True, exist_ok=True)

SUPPORTED_EXTENSIONS: Final[FrozenSet[str]] = frozenset({
    ".py", ".js", ".ts", ".jsx", ".tsx", ".java", ".c", ".cpp", ".h", ".hpp",
    ".cs", ".go", ".rs", ".rb", ".php", ".swift", ".kt", ".sh", ".bash",
    ".zsh", ".sql", ".html", ".htm", ".css", ".scss", ".json", ".yaml",
    ".yml", ".toml", ".ini", ".cfg", ".txt", ".md", ".lua", ".dart", ".r", ".m",
})

_SKIP_DIRS: Final[FrozenSet[str]] = frozenset({
    ".git", ".hg", ".svn", "__pycache__", "node_modules", ".venv", "venv",
    ".env", ".idea", ".vscode", "dist", "build", ".tox", ".mypy_cache",
    ".pytest_cache", ".next", ".nuxt", "target", "vendor", ".bundle",
})

EXT_TO_LANGUAGE: Final[Dict[str, str]] = {
    ".py": "Python", ".js": "JavaScript", ".jsx": "JavaScript",
    ".ts": "TypeScript", ".tsx": "TypeScript", ".java": "Java",
    ".c": "CFamily", ".cpp": "CFamily", ".h": "CFamily",
    ".hpp": "CFamily", ".cs": "CSharp", ".go": "Go", ".rs": "Rust",
    ".rb": "Ruby", ".php": "PHP", ".swift": "CFamily", ".kt": "Java",
    ".sh": "Bash", ".bash": "Bash", ".zsh": "Bash", ".sql": "SQL",
    ".html": "HTML", ".htm": "HTML", ".css": "CSS", ".scss": "CSS",
    ".json": "JSON", ".yaml": "YAML", ".yml": "YAML",
    ".md": "Markdown", ".txt": "Text",
}


# ═══════════════════════════════════════════════════════════════════
# SECTION 4 — THEME & COLOR MANAGEMENT
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True, slots=True)
class Theme:
    name: str
    background: str
    foreground: str
    comment: str
    keyword: str
    string: str
    number: str
    function: str
    builtin: str
    decorator: str
    operator: str
    class_name: str
    line_number: str
    current_line: str
    cursor: str
    title_bar: str
    title_text: str
    window_border: str
    junior_accent: str
    senior_accent: str

    def to_dict(self) -> Dict[str, str]:
        return {k: v for k, v in asdict(self).items() if k != "name"}

    @classmethod
    def from_dict(cls, name: str, d: Dict[str, str]) -> "Theme":
        return cls(name=name, **{k: d.get(k, "#ffffff") for k in
                                 cls.__dataclass_fields__ if k != "name"})

class ThemeRegistry:
    _instance: Optional["ThemeRegistry"] = None
    _lock = threading.Lock()

    def __new__(cls) -> "ThemeRegistry":
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._themes: Dict[str, Theme] = {}
                    cls._instance._qcolor_cache: Dict[Tuple[str, str], QColor] = {}
                    cls._instance._load_defaults()
        return cls._instance

    def _load_defaults(self) -> None:
        _RAW_THEMES: Dict[str, Dict[str, str]] = {
            "Tokyo Night": {"background": "#16171e", "foreground": "#c0caf5", "comment": "#565f89", "keyword": "#bb9af7", "string": "#9ece6a", "number": "#ff9e64", "function": "#7aa2f7", "builtin": "#7aa2f7", "decorator": "#e0af68", "operator": "#89ddff", "class_name": "#7dcfff", "line_number": "#3b4261", "current_line": "#1a1b26", "cursor": "#c0caf5", "title_bar": "#1a1b26", "title_text": "#7aa2f7", "window_border": "#16171e", "junior_accent": "#7aa2f7", "senior_accent": "#9ece6a"},
            "Dracula": {"background": "#282a36", "foreground": "#f8f8f2", "comment": "#6272a4", "keyword": "#ff79c6", "string": "#f1fa8c", "number": "#bd93f9", "function": "#50fa7b", "builtin": "#8be9fd", "decorator": "#50fa7b", "operator": "#ff79c6", "class_name": "#8be9fd", "line_number": "#6272a4", "current_line": "#44475a", "cursor": "#f8f8f2", "title_bar": "#21222c", "title_text": "#8be9fd", "window_border": "#191a21", "junior_accent": "#8be9fd", "senior_accent": "#50fa7b"},
            "Monokai": {"background": "#272822", "foreground": "#f8f8f2", "comment": "#75715e", "keyword": "#f92672", "string": "#e6db74", "number": "#ae81ff", "function": "#a6e22e", "builtin": "#66d9ef", "decorator": "#a6e22e", "operator": "#f92672", "class_name": "#66d9ef", "line_number": "#75715e", "current_line": "#3e3d32", "cursor": "#f8f8f2", "title_bar": "#1e1f1c", "title_text": "#a6e22e", "window_border": "#1e1f1c", "junior_accent": "#66d9ef", "senior_accent": "#a6e22e"},
            "One Dark": {"background": "#282c34", "foreground": "#abb2bf", "comment": "#5c6370", "keyword": "#c678dd", "string": "#98c379", "number": "#d19a66", "function": "#61afef", "builtin": "#e5c07b", "decorator": "#56b6c2", "operator": "#c678dd", "class_name": "#e5c07b", "line_number": "#4b5263", "current_line": "#2c313c", "cursor": "#528bff", "title_bar": "#21252b", "title_text": "#61afef", "window_border": "#181a1f", "junior_accent": "#61afef", "senior_accent": "#98c379"},
            "GitHub Dark": {"background": "#0d1117", "foreground": "#c9d1d9", "comment": "#8b949e", "keyword": "#ff7b72", "string": "#a5d6ff", "number": "#79c0ff", "function": "#d2a8ff", "builtin": "#ffa657", "decorator": "#ffa657", "operator": "#ff7b72", "class_name": "#ffa657", "line_number": "#484f58", "current_line": "#161b22", "cursor": "#58a6ff", "title_bar": "#010409", "title_text": "#58a6ff", "window_border": "#010409", "junior_accent": "#58a6ff", "senior_accent": "#7ee787"},
            "Nord": {"background": "#2e3440", "foreground": "#d8dee9", "comment": "#616e88", "keyword": "#81a1c1", "string": "#a3be8c", "number": "#b48ead", "function": "#88c0d0", "builtin": "#81a1c1", "decorator": "#ebcb8b", "operator": "#81a1c1", "class_name": "#8fbcbb", "line_number": "#4c566a", "current_line": "#3b4252", "cursor": "#d8dee9", "title_bar": "#3b4252", "title_text": "#88c0d0", "window_border": "#2e3440", "junior_accent": "#88c0d0", "senior_accent": "#a3be8c"},
            "Gruvbox": {"background": "#282828", "foreground": "#ebdbb2", "comment": "#928374", "keyword": "#fb4934", "string": "#b8bb26", "number": "#d3869b", "function": "#fabd2f", "builtin": "#fe8019", "decorator": "#fe8019", "operator": "#fb4934", "class_name": "#fabd2f", "line_number": "#7c6f64", "current_line": "#3c3836", "cursor": "#ebdbb2", "title_bar": "#3c3836", "title_text": "#fabd2f", "window_border": "#282828", "junior_accent": "#fabd2f", "senior_accent": "#b8bb26"},
            "Solarized Dark": {"background": "#002b36", "foreground": "#839496", "comment": "#586e75", "keyword": "#859900", "string": "#2aa198", "number": "#d33682", "function": "#268bd2", "builtin": "#b58900", "decorator": "#cb4b16", "operator": "#859900", "class_name": "#b58900", "line_number": "#073642", "current_line": "#073642", "cursor": "#839496", "title_bar": "#073642", "title_text": "#268bd2", "window_border": "#002b36", "junior_accent": "#268bd2", "senior_accent": "#859900"},
            "Catppuccin": {"background": "#24273a", "foreground": "#cad3f5", "comment": "#6e738d", "keyword": "#c6a0f6", "string": "#a6da95", "number": "#f5a97f", "function": "#8aadf4", "builtin": "#8bd5ca", "decorator": "#f5a97f", "operator": "#91d7e3", "class_name": "#8bd5ca", "line_number": "#494d64", "current_line": "#363a4f", "cursor": "#cad3f5", "title_bar": "#363a4f", "title_text": "#8aadf4", "window_border": "#24273a", "junior_accent": "#8aadf4", "senior_accent": "#a6da95"},
        }
        for name, d in _RAW_THEMES.items():
            self._themes[name] = Theme.from_dict(name, d)

    def get(self, name: str) -> Theme:
        return self._themes.get(name, self._themes["Dracula"])

    def names(self) -> List[str]:
        return list(self._themes.keys())

    def qcolor(self, theme_name: str, key: str) -> QColor:
        cache_key = (theme_name, key)
        cached = self._qcolor_cache.get(cache_key)
        if cached is not None:
            return cached
        theme = self.get(theme_name)
        val = getattr(theme, key, "#ffffff")
        qc = QColor(val)
        self._qcolor_cache[cache_key] = qc
        return qc


THEMES: Dict[str, Dict[str, str]] = {
    name: theme.to_dict() for name, theme in ThemeRegistry()._themes.items()
}


# ═══════════════════════════════════════════════════════════════════
# SECTION 5 — LANGUAGE TOKENIZER
# ═══════════════════════════════════════════════════════════════════

_LANG_DATA: Dict[str, dict] = {
    "Python": {"keywords": {"False","None","True","and","as","assert","async","await","break","class","continue","def","del","elif","else","except","finally","for","from","global","if","import","in","is","lambda","nonlocal","not","or","pass","raise","return","try","while","with","yield"}, "builtins": {"print","len","range","int","str","float","list","dict","set","tuple","bool","type","isinstance","enumerate","zip","map","filter","sorted","reversed","open","super","property","staticmethod","classmethod","abs","max","min","sum","any","all","hash","id","input","format","hex","oct","bin","round","pow","divmod","chr","ord","repr","vars","dir","getattr","setattr","hasattr","delattr","callable","iter","next"}, "extra_patterns": [("decorator", r"@\w+(\.\w+)*"), ("fstring", r"\b(?:f|r|b|fr|rf|br|rb)(?:\"\"\"[\s\S]*?\"\"\"|\'\'\'[\s\S]*?\'\'\'|\"(?:[^\"\\]|\\.)*\"|\'(?:[^\'\\]|\\.)*\')")], "comment": r"#[^\n]*", "string": r'"""[\s\S]*?"""|\'\'\'[\s\S]*?\'\'\'|"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b|0o[0-7]+\b"},
    "JavaScript": {"keywords": {"break","case","catch","class","const","continue","debugger","default","delete","do","else","export","extends","finally","for","function","if","import","in","instanceof","let","new","of","return","static","super","switch","this","throw","try","typeof","var","void","while","with","yield","async","await","from","as","null","undefined"}, "builtins": {"console","Math","JSON","Array","Object","String","Number","Boolean","Date","RegExp","Error","Map","Set","Promise","Symbol","Proxy","Reflect","parseInt","parseFloat","isNaN","isFinite","encodeURI","decodeURI","setTimeout","setInterval","clearTimeout","clearInterval","fetch","document","window","require","module","process","Buffer","true","false"}, "extra_patterns": [], "comment": r"//[^\n]*|/\*[\s\S]*?\*/", "string": r'`(?:[^`\\]|\\.)*`|"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b|0o[0-7]+\b"},
    "TypeScript": "JavaScript",
    "CFamily": {"keywords": {"auto","break","case","char","const","continue","default","do","double","else","enum","extern","float","for","goto","if","inline","int","long","register","return","short","signed","sizeof","static","struct","switch","typedef","union","unsigned","void","volatile","while","class","namespace","template","typename","public","private","protected","virtual","override","final","new","delete","try","catch","throw","using","true","false","nullptr","boolean","byte","extends","implements","import","instanceof","interface","native","package","super","synchronized","this","throws","transient","abstract","assert"}, "builtins": {"printf","scanf","malloc","free","sizeof","strlen","std","cout","cin","endl","string","vector","map","set","println","System","Math"}, "extra_patterns": [("preprocessor", r"^\s*#[^\n]*")], "comment": r"//[^\n]*|/\*[\s\S]*?\*/", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b"},
    "CSharp": {"keywords": {"abstract","as","base","bool","break","byte","case","catch","char","checked","class","const","continue","decimal","default","delegate","do","double","else","enum","event","explicit","extern","false","finally","fixed","float","for","foreach","goto","if","implicit","in","int","interface","internal","is","lock","long","namespace","new","null","object","operator","out","override","params","private","protected","public","readonly","ref","return","sbyte","sealed","short","sizeof","stackalloc","static","string","struct","switch","this","throw","true","try","typeof","uint","ulong","unchecked","unsafe","ushort","using","virtual","void","volatile","while","async","await","yield","var","dynamic","get","set","value","nameof","when","where","global","record","init"}, "builtins": {"Console","Math","Convert","String","Array","List","Dictionary","HashSet","Task","Thread","Exception","InvalidOperationException","DateTime","TimeSpan","Guid","StringBuilder","Random","Regex","IEnumerable","IEnumerator","IDisposable","Action","Func","Tuple"}, "extra_patterns": [("preprocessor", r"^\s*#[^\n]*"), ("decorator", r"\[[\w\s,\.()=]*\]")], "comment": r"//[^\n]*|/\*[\s\S]*?\*/", "string": r'\$?@"[^"]*"|@"[^"]*"|"(?:[^"\\]|\\.)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*[fFdDmM]?\b|0x[0-9a-fA-F]+\b|0b[01]+\b"},
    "Java": {"keywords": {"abstract","assert","boolean","break","byte","case","catch","char","class","const","continue","default","do","double","else","enum","extends","final","finally","float","for","goto","if","implements","import","instanceof","int","interface","long","native","new","package","private","protected","public","return","short","static","strictfp","super","switch","synchronized","this","throw","throws","transient","try","void","volatile","while","true","false","null","var","record","yield","sealed","permits","non-sealed"}, "builtins": {"System","Math","String","Integer","Double","Float","Long","Boolean","Character","Object","Class","Void","Exception","RuntimeException","ArrayList","LinkedList","HashMap","HashSet","TreeMap","TreeSet","Array","Arrays","Collections","List","Map","Set","Queue","Deque","Thread","Runnable","Callable","Future","Optional","Stream","Scanner","PrintWriter","BufferedReader","BufferedWriter"}, "extra_patterns": [("decorator", r"@\w+(\.\w+)*")], "comment": r"//[^\n]*|/\*[\s\S]*?\*/", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?[fFdDlL]?\b|0x[0-9a-fA-F]+\b|0b[01]+\b"},
    "Go": {"keywords": {"break","case","chan","const","continue","default","defer","else","fallthrough","for","func","go","goto","if","import","interface","map","package","range","return","select","struct","switch","type","var","nil","true","false","iota"}, "builtins": {"fmt","os","io","strings","strconv","math","time","len","cap","make","new","append","copy","delete","panic","recover","print","println","true","false","nil","iota"}, "extra_patterns": [], "comment": r"//[^\n]*|/\*[\s\S]*?\*/", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'|`[^`]*`', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b|0o[0-7]+\b"},
    "Rust": {"keywords": {"fn","let","mut","const","static","if","else","for","while","loop","match","return","break","continue","in","as","use","mod","pub","struct","enum","trait","impl","where","self","Self","super","crate","extern","ref","move","async","await","dyn","unsafe","true","false"}, "builtins": {"println","print","format","vec","String","Vec","Option","Result","Box","Rc","Arc","Some","None","Ok","Err","HashMap","BTreeMap","HashSet"}, "extra_patterns": [("macro", r"\b([a-zA-Z_]\w*)!"), ("lifetime", r"\'\w+")], "comment": r"//[^\n]*|/\*[\s\S]*?\*/", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b|0o[0-7]+\b"},
    "Ruby": {"keywords": {"def","end","if","elsif","else","unless","while","until","for","do","break","next","redo","retry","return","class","module","begin","rescue","ensure","raise","yield","self","super","nil","true","false","and","or","not","alias","attr_accessor","attr_reader","attr_writer","require","require_relative","include","extend","private","public","protected","defined?","BEGIN","END","__FILE__","__LINE__"}, "builtins": {"puts","print","p","pp","require","require_relative","include","attr_accessor","attr_reader","attr_writer","Integer","Float","String","Array","Hash","Object","Module","Class","Range","Regexp","Proc","lambda","binding","caller","catch","throw","loop","sleep","exit","abort","at_exit","fork","spawn","system","exec","open","File","Dir","IO","Socket","Thread","Mutex","ENV","ARGV","STDIN","STDOUT","STDERR"}, "extra_patterns": [("symbol", r":[a-zA-Z_]\w*"), ("variable", r"@@?[a-zA-Z_]\w*")], "comment": r"#[^\n]*", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'|:[a-zA-Z_]\w*', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b|0o[0-7]+\b"},
    "PHP": {"keywords": {"abstract","and","array","as","break","callable","case","catch","class","clone","const","continue","declare","default","do","echo","else","elseif","empty","enddeclare","endfor","endforeach","endif","endswitch","endwhile","extends","final","finally","fn","for","foreach","function","global","goto","if","implements","include","include_once","instanceof","insteadof","interface","isset","list","namespace","new","or","print","private","protected","public","require","require_once","return","static","switch","throw","trait","try","unset","use","var","while","xor","yield","true","false","null"}, "builtins": {"echo","print","array","isset","unset","include","require","strlen","strpos","str_replace","substr","count","sort","explode","implode","date","time","json_encode","json_decode","file_get_contents","file_put_contents","fopen","fclose","fread","fwrite","mysql_query","mysqli_query","PDO","session_start","$_GET","$_POST","$_SESSION","$_COOKIE","$_SERVER","$_REQUEST","$_FILES","$_ENV"}, "extra_patterns": [("variable", r"\$\w+")], "comment": r"//[^\n]*|/\*[\s\S]*?\*/|#[^\n]*", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b|0b[01]+\b"},
    "HTML": {"keywords": set(), "builtins": set(), "extra_patterns": [("tag", r"</?(\w+)"), ("attr", r"\b([a-zA-Z-]+)(?==)")], "comment": r"<!--[\s\S]*?-->", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*\b"},
    "CSS": {"keywords": set(), "builtins": set(), "extra_patterns": [("selector", r"[#.]?[\w-]+(?=\s*\{)"), ("property", r"\b[\w-]+(?=\s*:)"), ("hex_color", r"#[0-9a-fA-F]{3,8}\b"), ("variable", r"--[\w-]+")], "comment": r"/\*[\s\S]*?\*/", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*(?:px|em|rem|vw|vh|%|s|ms|deg|fr|pt|pc|in|cm|mm)?\b"},
    "SQL": {"keywords": {"SELECT","FROM","WHERE","INSERT","INTO","VALUES","UPDATE","SET","DELETE","CREATE","TABLE","ALTER","DROP","INDEX","VIEW","JOIN","INNER","LEFT","RIGHT","OUTER","ON","GROUP","BY","HAVING","ORDER","ASC","DESC","LIMIT","OFFSET","DISTINCT","UNION","ALL","AS","AND","OR","NOT","IN","EXISTS","BETWEEN","LIKE","IS","NULL","PRIMARY","KEY","FOREIGN","REFERENCES","UNIQUE","DEFAULT","CHECK","CONSTRAINT","BEGIN","COMMIT","ROLLBACK","TRANSACTION","CASE","WHEN","THEN","ELSE","END"}, "builtins": {"COUNT","SUM","AVG","MIN","MAX","CONCAT","SUBSTRING","UPPER","LOWER","LENGTH","TRIM","ROUND","NOW","DATE","TIME","TIMESTAMP","VARCHAR","INT","INTEGER","FLOAT","DOUBLE","BOOLEAN","TEXT","BLOB"}, "extra_patterns": [], "comment": r"--[^\n]*|/\*[\s\S]*?\*/", "string": r"'[^'\\]*(?:\\.[^'\\]*)*'", "number": r"\b\d+\.?\d*\b"},
    "Bash": {"keywords": {"if","then","else","elif","fi","for","do","done","while","until","case","esac","function","in","return","break","continue","exit","local","export","readonly","unset","shift","source","alias"}, "builtins": {"echo","printf","read","set","trap","kill","jobs","bg","fg","wait","cd","pwd","ls","mkdir","rmdir","rm","cp","mv","cat","grep","awk","sed","find","xargs","which","whoami","hostname","date","sleep"}, "extra_patterns": [("variable", r"\$\w+|\$\{[^}]+\}")], "comment": r"#[^\n]*", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b\d+\.?\d*\b"},
    "JSON": {"keywords": set(), "builtins": set(), "extra_patterns": [("property", r'"([^"\\]|\\.)*"(?=\s*:)')], "comment": r"\/\/[^\n]*", "string": r'"([^"\\]|\\.)*"', "number": r"\b-?\d+\.?\d*(?:e[+-]?\d+)?\b"},
    "YAML": {"keywords": set(), "builtins": set(), "extra_patterns": [("property", r"\b[\w-]+(?=\s*:)")], "comment": r"#[^\n]*", "string": r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'', "number": r"\b-?\d+\.?\d*\b"},
    "Markdown": {"keywords": set(), "builtins": set(), "extra_patterns": [("heading", r"^#{1,6}[^\n]*"), ("bold", r"\*\*[\s\S]*?\*\*|__[\s\S]*?__"), ("italic", r"\*[\s\S]*?\*|_[\s\S]*_"), ("code", r"```[\s\S]*?```|`[^`\n]*`"), ("link", r"\[([^\]]+)\]\(([^)]+)\)")], "comment": r"", "string": r"", "number": r""},
    "Text": {"keywords": set(), "builtins": set(), "extra_patterns": [], "comment": r"", "string": r"", "number": r""},
}

for _k, _v in list(_LANG_DATA.items()):
    if isinstance(_v, str) and _v in _LANG_DATA:
        _LANG_DATA[_k] = _LANG_DATA[_v]


@runtime_checkable
class TokenizerProtocol(Protocol):
    def tokenize(self, text: str, lang: str) -> List[Tuple[str, str]]: ...


class RegexTokenizer:
    __slots__ = ()
    _compiled: Dict[str, re.Pattern] = {}
    _lock = threading.Lock()

    @classmethod
    def _compile(cls, lang: str) -> re.Pattern:
        cached = cls._compiled.get(lang)
        if cached is not None:
            return cached
        with cls._lock:
            cached = cls._compiled.get(lang)
            if cached is not None:
                return cached
            data = _LANG_DATA.get(lang, _LANG_DATA["Text"])
            patterns: List[Tuple[str, str]] = list(data.get("extra_patterns", []))
            patterns.extend([
                ("comment", data["comment"]),
                ("string", data["string"]),
                ("number", data["number"]),
                ("keyword", r"\b(?:" + "|".join(data.get("keywords", set())) + r")\b"),
                ("builtin", r"\b(?:" + "|".join(data.get("builtins", set())) + r")\b"),
                ("boolean", r"\b(?:true|false|null|True|False|None|nil|undefined)\b"),
                ("constant", r"\b[A-Z_][A-Z0-9_]+\b"),
                ("function", r"\b([a-zA-Z_]\w*)\s*(?=\()"),
                ("class_name", r"\b([A-Z]\w*)\b"),
                ("identifier", r"\b[a-zA-Z_]\w*\b"),
                ("operator", r"[+\-*/%=<>!&|^~]+"),
                ("bracket", r"[(){}\[\]]"),
                ("punctuation", r"[;:,.]"),
                ("whitespace", r"\s+"),
                ("other", r"."),
            ])
            valid = [(n, p) for n, p in patterns if p]
            pat_str = "|".join(f"(?P<{n}>{p})" for n, p in valid)
            compiled = re.compile(pat_str, re.MULTILINE | re.DOTALL)
            cls._compiled[lang] = compiled
            return compiled

    @classmethod
    def tokenize(cls, text: str, lang: str) -> List[Tuple[str, str]]:
        compiled = cls._compiled.get(lang) or cls._compile(lang)
        return [(m.lastgroup, m.group()) for m in compiled.finditer(text)]

    @classmethod
    def find_structural_markers(cls, text: str, lang: str) -> List[Tuple[int, str, str]]:
        """Find def/class/sections markers for YouTube chapters."""
        markers: List[Tuple[int, str, str]] = []
        pos = 0
        for tt, tx in cls.tokenize(text, lang):
            if tt == "keyword" and tx in ("def", "class", "func", "fn"):
                nc = text[pos + len(tx):pos + len(tx) + 80]
                m = re.match(r"\s+(\w+)", nc)
                if m:
                    nm = m.group(1)
                    kind = "class" if tx in ("class",) else "def"
                    markers.append((pos, kind, f"{tx} {nm}{'()' if kind != 'class' else ''}"))
            elif tt == "comment":
                s = tx.strip()
                if s.startswith("/*") and s.endswith("*/"):
                    s = s[2:-2].strip()
                elif s.startswith("//"):
                    s = s[2:].strip()
                elif s.startswith("#"):
                    s = s[1:].strip()
                elif s.startswith("--"):
                    s = s[2:].strip()
                if (5 <= len(s) <= 120 and
                    not s.startswith("!") and
                    not s.startswith("encoding") and
                    not s.startswith("coding") and
                    not s.startswith("type:") and
                    not s.startswith("noqa") and
                    not s.startswith("pragma") and
                    not s.startswith("pylint")):
                    markers.append((pos, "section", s))
            pos += len(tx)
        return markers


Tokenizer: TokenizerProtocol = RegexTokenizer()


# ═══════════════════════════════════════════════════════════════════
# SECTION 6 — DSP ENGINE
# ═══════════════════════════════════════════════════════════════════

try:
    from scipy.signal import lfilter as _scipy_lfilter, fftconvolve as _scipy_fftconvolve
    _HAS_SCIPY = True
except ImportError:
    _HAS_SCIPY = False

try:
    import numba
    _HAS_NUMBA = True
except ImportError:
    _HAS_NUMBA = False


if _HAS_NUMBA:
    @numba.njit(cache=True)
    def _nb_mix(mix, flat, offsets, lengths, starts):
        n_mix, n_flat = mix.shape[0], flat.shape[0]
        for i in range(len(starts)):
            s, ln, o = starts[i], lengths[i], offsets[i]
            for j in range(ln):
                if s + j < n_mix and o + j < n_flat:
                    mix[s + j] += flat[o + j]

    @numba.njit(cache=True)
    def _nb_env_follower(env, attack_coeff, release_coeff):
        n = len(env)
        out = np.empty(n, dtype=np.float32)
        current = 0.0
        for i in range(n):
            if env[i] > current:
                current = current * attack_coeff + env[i] * (1.0 - attack_coeff)
            else:
                current = current * release_coeff + env[i] * (1.0 - release_coeff)
            out[i] = current
        return out

    @numba.njit(cache=True)
    def _nb_apply_gain(x, smooth_env, target_lin, ratio):
        n = len(x)
        out = np.empty(n, dtype=np.float32)
        for i in range(n):
            if smooth_env[i] > target_lin:
                g = 1.0 - (1.0 - 1.0 / ratio) * (1.0 - target_lin / smooth_env[i])
            else:
                g = 1.0
            out[i] = x[i] * g
        return out

    @numba.njit(cache=True)
    def _nb_lookahead_gain(smooth_env, target_lin):
        n = len(smooth_env)
        gain = np.ones(n, dtype=np.float32)
        for i in range(n):
            if smooth_env[i] > target_lin:
                gain[i] = target_lin / smooth_env[i]
        return gain


class DSP:
    """Digital Signal Processing utilities — all static methods."""

    @staticmethod
    def env_exp(n: int, sr: int, attack: float = 0.001,
                decay_rate: float = 30.0, attack_curve: float = 2.0) -> np.ndarray:
        t = np.arange(n, dtype=np.float32) / sr
        env = np.exp(-t * decay_rate)
        a_samp = max(1, int(attack * sr))
        if a_samp < n:
            a_env = np.linspace(0, 1, a_samp, dtype=np.float32) ** attack_curve
            env[:a_samp] = a_env * np.exp(-np.arange(a_samp, dtype=np.float32) / sr * decay_rate)
        return env

    @staticmethod
    def fir_lowpass(cutoff: float, sr: int = 44100,
                    n_taps: int = 127, window: str = "blackman") -> np.ndarray:
        if n_taps % 2 == 0:
            n_taps += 1
        fc = cutoff / sr
        n = np.arange(n_taps, dtype=np.float32)
        center = (n_taps - 1) / 2.0
        h = np.sinc(2 * fc * (n - center))
        match window:
            case "blackman":
                w = (0.42 - 0.5 * np.cos(2 * np.pi * n / (n_taps - 1))
                     + 0.08 * np.cos(4 * np.pi * n / (n_taps - 1)))
            case "hamming":
                w = 0.54 - 0.46 * np.cos(2 * np.pi * n / (n_taps - 1))
            case "hann":
                w = 0.5 - 0.5 * np.cos(2 * np.pi * n / (n_taps - 1))
            case _:
                w = np.ones(n_taps, dtype=np.float32)
        h *= w
        s = np.sum(h)
        if s > 0:
            h /= s
        return h

    @staticmethod
    def fir_highpass(cutoff: float, sr: int = 44100,
                     n_taps: int = 127, window: str = "blackman") -> np.ndarray:
        hlp = DSP.fir_lowpass(cutoff, sr, n_taps, window)
        h = -hlp
        h[len(h) // 2] += 1.0
        return h

    @staticmethod
    def fir_bandpass(low: float, high: float, sr: int = 44100,
                     n_taps: int = 255, window: str = "blackman") -> np.ndarray:
        return DSP.fir_lowpass(high, sr, n_taps, window) - DSP.fir_lowpass(low, sr, n_taps, window)

    @staticmethod
    def iir_lowpass(x: np.ndarray, cutoff: float, sr: int = 44100) -> np.ndarray:
        if not _HAS_SCIPY or len(x) == 0:
            return x
        alpha = math.exp(-2.0 * math.pi * cutoff / sr)
        return _scipy_lfilter([1.0 - alpha], [1.0, -alpha], x).astype(np.float32)

    @staticmethod
    def convolve(x: np.ndarray, h: np.ndarray) -> np.ndarray:
        n, nh = len(x), len(h)
        if nh <= 1:
            return x * h[0] if nh == 1 else x
        if _HAS_SCIPY and nh > 64:
            return _scipy_fftconvolve(x, h, mode='full')[:n].astype(np.float32)
        if nh < 64 and n < 2048:
            return np.convolve(x, h, mode='full')[:n].astype(np.float32)
        MAX_FFT_BITS = 20
        total = n + nh - 1
        if total.bit_length() <= MAX_FFT_BITS:
            n_fft = 1 << total.bit_length()
            return np.fft.irfft(np.fft.rfft(x, n_fft) * np.fft.rfft(h, n_fft), n_fft)[:n].astype(np.float32)
        n_fft = 1 << MAX_FFT_BITS
        block = n_fft - nh + 1
        H = np.fft.rfft(h, n_fft)
        out = np.zeros(total, dtype=np.float32)
        for i in range(0, n, block):
            end = min(i + block, n)
            yb = np.fft.irfft(np.fft.rfft(x[i:end], n_fft) * H, n_fft)
            out[i:i + min(len(yb), total - i)] += yb[:min(len(yb), total - i)]
        return out[:n].astype(np.float32)

    @staticmethod
    def filt_lp(x, c, sr=44100, n_taps=127):
        return DSP.convolve(x, DSP.fir_lowpass(c, sr, n_taps))

    @staticmethod
    def filt_hp(x, c, sr=44100, n_taps=127):
        return DSP.convolve(x, DSP.fir_highpass(c, sr, n_taps))

    @staticmethod
    def filt_bp(x, l, h, sr=44100, n_taps=255):
        return DSP.convolve(x, DSP.fir_bandpass(l, h, sr, n_taps))

    @staticmethod
    def filt_resonator(x, f, q, sr=44100, gain=1.0):
        w0 = 2 * np.pi * f / sr
        r = np.exp(-w0 / (2 * max(0.5, q)))
        wd = w0 * np.sqrt(max(0.0, 1.0 - 1.0 / (4 * q * q))) if q > 0.5 else w0
        n_ir = min(len(x), max(16, int(sr * max(0.005, 6.0 * q / max(1.0, f)))))
        t = np.arange(n_ir, dtype=np.float32)
        ir = (r ** t) * np.sin(wd * t)
        p = np.max(np.abs(ir))
        if p > 1e-10:
            ir = ir / p * gain
        return DSP.convolve(x, ir)

    @staticmethod
    def sat_tube(x, drive=1.0):
        if drive <= 0:
            return x
        return (np.tanh(x * drive) / max(0.001, np.tanh(drive))).astype(np.float32)

    @staticmethod
    def sat_hard(x, t=1.0):
        return np.clip(x, -t, t).astype(np.float32)

    @staticmethod
    def sat_oversampled(x, drive=1.5):
        if drive <= 0:
            return x
        n = len(x)
        if n < 2:
            return DSP.sat_tube(x, drive)
        x_up = np.zeros(n * 2, dtype=np.float32)
        x_up[0::2] = x
        x_up[1:-1:2] = (x[:-1] + x[1:]) / 2.0
        x_up[-1] = x[-1]
        y_up = DSP.sat_tube(x_up, drive)
        y_down = (y_up[0:-1:2] + y_up[1::2]) / 2.0
        return y_down[:n].astype(np.float32)

    @staticmethod
    def exciter(x, sr=44100, amount=0.5):
        hp = DSP.filt_hp(x, 4000, sr, n_taps=127)
        return x + DSP.filt_lp(DSP.sat_tube(hp, 2.0), 12000, sr, n_taps=63) * amount

    @staticmethod
    def binaural_pan(mono, pan, sr=44100):
        if abs(pan) < 0.01:
            return mono.copy(), mono.copy()
        if pan > 0:
            left = DSP.iir_lowpass(mono, 6000, sr) * (1.0 - pan * 0.6)
            right = mono * min(1.0, 1.0 + pan * 0.2)
        else:
            right = DSP.iir_lowpass(mono, 6000, sr) * (1.0 + pan * 0.6)
            left = mono * min(1.0, 1.0 - pan * 0.2)
        itd_samp = int(abs(pan) * 0.0006 * sr)
        l_out = np.zeros(len(mono) + itd_samp, dtype=np.float32)
        r_out = np.zeros(len(mono) + itd_samp, dtype=np.float32)
        if pan > 0:
            l_out[itd_samp:itd_samp + len(left)] += left
            r_out[:len(mono)] += right
        else:
            r_out[itd_samp:itd_samp + len(right)] += right
            l_out[:len(mono)] += left
        return l_out, r_out

    @staticmethod
    def compressor_rms(x, sr, threshold_db=-12.0, ratio=3.0,
                        attack_ms=10, release_ms=100):
        if threshold_db >= 0 or ratio <= 1:
            return x.astype(np.float32)
        target_lin = 10 ** (threshold_db / 20)
        env = np.abs(x).astype(np.float32)
        ac = np.exp(-1.0 / (sr * (attack_ms / 1000.0)))
        rc = np.exp(-1.0 / (sr * (release_ms / 1000.0)))
        if _HAS_NUMBA:
            smooth_env = _nb_env_follower(env, ac, rc)
            return _nb_apply_gain(x.astype(np.float32), smooth_env, target_lin, ratio)
        if _HAS_SCIPY:
            env_a = _scipy_lfilter([1 - ac], [1, -ac], env)
            env_r = _scipy_lfilter([1 - rc], [1, -rc], env)
            smooth_env = np.maximum(env_a, env_r).astype(np.float32)
        else:
            smooth_env = env
        gain = np.ones_like(x, dtype=np.float32)
        mask = smooth_env > target_lin
        gain[mask] = 1.0 - (1.0 - 1.0 / ratio) * (1.0 - target_lin / smooth_env[mask])
        return (x * gain).astype(np.float32)

    @staticmethod
    def lookahead_limiter(x, sr=44100, threshold_db=-1.0, release_ms=50):
        target_lin = 10 ** (threshold_db / 20)
        peak = np.max(np.abs(x))
        if peak <= target_lin:
            return x.astype(np.float32)
        ac = np.exp(-1.0 / (sr * 0.001))
        rc = np.exp(-1.0 / (sr * (release_ms / 1000.0)))
        env = np.abs(x).astype(np.float32)
        if _HAS_NUMBA:
            smooth_env = _nb_env_follower(env, ac, rc)
            gain = _nb_lookahead_gain(smooth_env, target_lin)
        else:
            gain = np.ones_like(x, dtype=np.float32)
            mask = env > target_lin
            gain[mask] = target_lin / env[mask]
        lookahead = int(sr * 0.002)
        if lookahead > 0 and len(gain) > lookahead:
            gain = np.roll(gain, -lookahead)
            gain[-lookahead:] = gain[-lookahead - 1]
        return (x * gain).astype(np.float32)

    @staticmethod
    def dc_block(x, sr=44100):
        return DSP.filt_hp(x, 20.0, sr, n_taps=63)

    @staticmethod
    def osc_sine(f, n, sr, phase=0.0):
        return np.sin(2 * np.pi * f * (np.arange(n, dtype=np.float32) / sr) + phase).astype(np.float32)

    @staticmethod
    def osc_sweep(f1, f2, n, sr):
        if n <= 0:
            return np.zeros(0, dtype=np.float32)
        if f1 <= 0: f1 = 1.0
        if f2 <= 0: f2 = 1.0
        t = np.arange(n, dtype=np.float32) / sr
        freq = f1 * (f2 / f1) ** (t / (n / sr))
        return np.sin(2 * np.pi * np.cumsum(freq) / sr).astype(np.float32)

    @staticmethod
    def osc_fm(c, mr, mi, n, sr, phase=0.0):
        t = np.arange(n, dtype=np.float32) / sr
        return np.sin(2 * np.pi * c * t + mi * np.sin(2 * np.pi * c * mr * t) + phase).astype(np.float32)

    @staticmethod
    def osc_fm_multi(c, mrs, mis, n, sr):
        t = np.arange(n, dtype=np.float32) / sr
        ph = 2 * np.pi * c * t
        for mr, mi in zip(mrs, mis):
            ph += mi * np.sin(2 * np.pi * c * mr * t)
        return np.sin(ph).astype(np.float32)

    @staticmethod
    def osc_saw(f, n, sr):
        t = np.arange(n, dtype=np.float32) / sr
        sig = np.zeros(n, dtype=np.float32)
        for h in range(1, 17):
            fh = f * h
            if fh >= sr * 0.45:
                break
            sig += np.sin(2 * np.pi * fh * t) / h
        return (sig * 0.5).astype(np.float32)

    @staticmethod
    def noise_white(n, rng):
        return rng.randn(n).astype(np.float32)

    @staticmethod
    def noise_pink(n, rng, sr=44100):
        bs = min(n, sr * 5)
        white = rng.randn(bs).astype(np.float32)
        fft = np.fft.rfft(white)
        freqs = np.fft.rfftfreq(bs, 1.0 / sr)
        if len(freqs) > 1:
            freqs[0] = max(freqs[1], 1.0)
            fft[1:] /= np.sqrt(np.abs(freqs[1:]))
            fft[0] = 0
        pink = np.fft.irfft(fft, n=bs).astype(np.float32)
        p = np.max(np.abs(pink))
        if p > 1e-6:
            pink /= p
        reps, rem = n // bs, n % bs
        out = np.tile(pink, reps) if reps > 0 else np.array([], dtype=np.float32)
        if rem > 0:
            out = np.concatenate([out, pink[:rem]])
        return out

    @staticmethod
    def noise_brown(n, rng):
        white = rng.randn(n).astype(np.float32)
        brown = np.cumsum(white) - np.mean(np.cumsum(white))
        p = np.max(np.abs(brown))
        if p > 0:
            brown = brown / p
        return (brown * 0.5).astype(np.float32)

    @staticmethod
    def modal(modes, n, sr, inharmonicity=0.0):
        t = np.arange(n, dtype=np.float32) / sr
        out = np.zeros(n, dtype=np.float32)
        f0 = modes[0][0] if modes else 440.0
        for freq, decay, amp in modes:
            af = freq
            if inharmonicity > 0:
                nh = freq / f0
                af = freq * np.sqrt(1 + inharmonicity * nh * nh)
            out += np.sin(2 * np.pi * af * t) * np.exp(-decay * t) * amp
        p = np.max(np.abs(out))
        if p > 1e-6:
            out /= p
        return out

    @staticmethod
    def normalize(x, target_db=-1.0):
        p = np.max(np.abs(x))
        if p < 1e-10:
            return x
        return x * (10 ** (target_db / 20) / p)

    @staticmethod
    def to_int16(x, target_db=-1.0):
        x = DSP.normalize(x, target_db)
        x = DSP.sat_hard(x, 1.0)
        np.nan_to_num(x, copy=False, nan=0.0, posinf=1.0, neginf=-1.0)
        return np.clip(x * 32767, -32768, 32767).astype(np.int16)

    @staticmethod
    def master_mono(x, sr=44100, target_db=-0.1):
        if len(x) == 0:
            return x
        x = DSP.dc_block(x, sr)
        x = DSP.filt_hp(x, 25.0, sr, n_taps=127)
        # Warm sub-bass
        sub = DSP.filt_bp(x, 40, 120, sr, n_taps=255)
        sub = DSP.sat_tube(sub * 1.4, 1.3)
        x = x + sub * 0.25
        # Body warmth
        x = x + DSP.filt_lp(x, 150, sr, n_taps=127) * 0.12
        x = x - DSP.filt_bp(x, 250, 500, sr, n_taps=255) * 0.12
        # Air
        x = x + DSP.filt_hp(x, 10000, sr, n_taps=63) * 0.20
        # Two-stage compression
        x = DSP.compressor_rms(x, sr, threshold_db=-22.0, ratio=1.8,
                                attack_ms=30, release_ms=220)
        x = DSP.compressor_rms(x, sr, threshold_db=-12.0, ratio=2.5,
                                attack_ms=8, release_ms=100)
        # Tube saturation
        x = DSP.sat_oversampled(x, drive=1.3)
        return np.clip(DSP.lookahead_limiter(x, sr, threshold_db=target_db), -1.0, 1.0).astype(np.float32)

    @staticmethod
    def master_stereo_asmr(mix_l, mix_r, sr=44100, target_db=-1.0):
        """Enhanced ASMR mastering: sub-bass warmth, de-essing, air band, two-stage comp."""
        if len(mix_l) == 0:
            return mix_l, mix_r
        # 1. Clean DC & rumble
        mix_l = DSP.dc_block(mix_l, sr)
        mix_r = DSP.dc_block(mix_r, sr)
        mix_l = DSP.filt_hp(mix_l, 25.0, sr, n_taps=127)
        mix_r = DSP.filt_hp(mix_r, 25.0, sr, n_taps=127)

        # 2. Warm sub-bass (40-120 Hz) for deep thock "chest" feel
        sub_l = DSP.filt_bp(mix_l, 40, 120, sr, n_taps=255)
        sub_r = DSP.filt_bp(mix_r, 40, 120, sr, n_taps=255)
        sub_l = DSP.sat_tube(sub_l * 1.4, 1.3)
        sub_r = DSP.sat_tube(sub_r * 1.4, 1.3)
        mix_l = mix_l + sub_l * 0.25
        mix_r = mix_r + sub_r * 0.25

        # 3. Mid-side: gentle low-pass on mid, slight side boost for width
        mid = (mix_l + mix_r) * 0.5
        side = (mix_l - mix_r) * 0.5
        mid = DSP.filt_lp(mid, 10000, sr, n_taps=127)
        side = side * 1.12
        mix_l = mid + side
        mix_r = mid - side

        # 4. Gentle de-esser (5-8 kHz) to tame harsh click transients
        ess_l = DSP.filt_bp(mix_l, 5000, 8500, sr, n_taps=255)
        ess_r = DSP.filt_bp(mix_r, 5000, 8500, sr, n_taps=255)
        ess_env_l = np.abs(ess_l).astype(np.float32)
        ess_env_r = np.abs(ess_r).astype(np.float32)
        ess_thresh = 0.12
        ess_gain_l = np.where(ess_env_l > ess_thresh,
                              ess_thresh / np.maximum(ess_env_l, 1e-10), 1.0).astype(np.float32)
        ess_gain_r = np.where(ess_env_r > ess_thresh,
                              ess_thresh / np.maximum(ess_env_r, 1e-10), 1.0).astype(np.float32)
        if _HAS_SCIPY:
            ess_gain_l = _scipy_lfilter([1.0], [1.0, -0.99], ess_gain_l).astype(np.float32)
            ess_gain_r = _scipy_lfilter([1.0], [1.0, -0.99], ess_gain_r).astype(np.float32)
        mix_l = mix_l - ess_l * (1.0 - ess_gain_l) * 0.4
        mix_r = mix_r - ess_r * (1.0 - ess_gain_r) * 0.4

        # 5. Soft tube saturation for analog warmth
        mix_l = DSP.sat_tube(mix_l, drive=1.25)
        mix_r = DSP.sat_tube(mix_r, drive=1.25)

        # 6. Two-stage gentle compression (ASMR-smooth, no pumping)
        mix_l = DSP.compressor_rms(mix_l, sr, threshold_db=-24.0, ratio=1.6,
                                    attack_ms=40, release_ms=250)
        mix_r = DSP.compressor_rms(mix_r, sr, threshold_db=-24.0, ratio=1.6,
                                    attack_ms=40, release_ms=250)
        mix_l = DSP.compressor_rms(mix_l, sr, threshold_db=-12.0, ratio=2.5,
                                    attack_ms=8, release_ms=100)
        mix_r = DSP.compressor_rms(mix_r, sr, threshold_db=-12.0, ratio=2.5,
                                    attack_ms=8, release_ms=100)

        # 7. Air band (11 kHz+) for subtle ASMR "tingles" — gentle exciter
        air_l = DSP.filt_hp(mix_l, 11000, sr, n_taps=63)
        air_r = DSP.filt_hp(mix_r, 11000, sr, n_taps=63)
        air_l = DSP.sat_tube(air_l, 1.8) * 0.5
        air_r = DSP.sat_tube(air_r, 1.8) * 0.5
        mix_l = mix_l + air_l * 0.15
        mix_r = mix_r + air_r * 0.15

        # 8. Gentle lookahead limiter
        mix_l = DSP.lookahead_limiter(mix_l, sr, threshold_db=target_db, release_ms=80)
        mix_r = DSP.lookahead_limiter(mix_r, sr, threshold_db=target_db, release_ms=80)
        return (np.clip(mix_l, -1.0, 1.0).astype(np.float32),
                np.clip(mix_r, -1.0, 1.0).astype(np.float32))


# ═══════════════════════════════════════════════════════════════════
# SECTION 7 — SOUND SYNTHESIS
# ═══════════════════════════════════════════════════════════════════

@dataclass(slots=True)
class Voice:
    osc: str = "sine"
    freq: float = 440.0
    freq_end: float = 0.0
    fm_ratio: float = 1.0
    fm_index: float = 0.0
    fm_ratios: Optional[List[float]] = None
    fm_indices: Optional[List[float]] = None
    attack: float = 0.001
    decay_rate: float = 30.0
    attack_curve: float = 2.0
    filt: str = "none"
    f_cutoff: float = 8000.0
    f_high: float = 12000.0
    f_q: float = 1.0
    drive: float = 0.0
    gain: float = 0.5
    delay: float = 0.0
    modes: Optional[List[Tuple[float, float, float]]] = None
    inharmonicity: float = 0.0


class OscillatorStrategy(Protocol):
    def generate(self, n: int, sr: int, **params) -> np.ndarray: ...


class SoundRenderer:
    __slots__ = ("sr",)

    def __init__(self, sr: int = 44100):
        self.sr = sr

    def render(self, voices: Sequence[Voice], duration: float,
               rng: np.random.RandomState) -> np.ndarray:
        n = int(self.sr * duration)
        if n <= 0:
            return np.zeros(0, dtype=np.float32)
        mix = np.zeros(n, dtype=np.float32)
        for v in voices:
            sig = self._render_voice(v, n, rng)
            d_samp = int(v.delay * self.sr)
            if d_samp > 0:
                if d_samp >= n:
                    continue
                sig = np.concatenate([np.zeros(d_samp, dtype=np.float32), sig[:n - d_samp]])
            if len(sig) < n:
                sig = np.concatenate([sig, np.zeros(n - len(sig), dtype=np.float32)])
            else:
                sig = sig[:n]
            mix += sig
        return DSP.dc_block(mix, self.sr)

    def _render_voice(self, v: Voice, n: int, rng: np.random.RandomState) -> np.ndarray:
        match v.osc:
            case "sine":       sig = DSP.osc_sine(v.freq, n, self.sr)
            case "sweep":      sig = DSP.osc_sweep(v.freq, v.freq_end, n, self.sr)
            case "fm":
                if v.fm_ratios:
                    sig = DSP.osc_fm_multi(v.freq, v.fm_ratios, v.fm_indices, n, self.sr)
                else:
                    sig = DSP.osc_fm(v.freq, v.fm_ratio, v.fm_index, n, self.sr)
            case "noise_white": sig = DSP.noise_white(n, rng)
            case "noise_pink":  sig = DSP.noise_pink(n, rng, self.sr)
            case "noise_brown": sig = DSP.noise_brown(n, rng)
            case "modal":
                sig = DSP.modal(v.modes, n, self.sr, v.inharmonicity) if v.modes else np.zeros(n, dtype=np.float32)
            case "saw":         sig = DSP.osc_saw(v.freq, n, self.sr)
            case _:             sig = np.zeros(n, dtype=np.float32)

        sig *= DSP.env_exp(n, self.sr, attack=v.attack, decay_rate=v.decay_rate, attack_curve=v.attack_curve)

        match v.filt:
            case "lp":         sig = DSP.filt_lp(sig, v.f_cutoff, self.sr)
            case "hp":         sig = DSP.filt_hp(sig, v.f_cutoff, self.sr)
            case "bp":         sig = DSP.filt_bp(sig, v.f_cutoff, v.f_high, self.sr)
            case "resonator":  sig = DSP.filt_resonator(sig, v.f_cutoff, v.f_q, self.sr)

        if v.drive > 0:
            sig = DSP.sat_tube(sig, v.drive)
        return sig * v.gain


class VoiceFactory:
    @staticmethod
    def click(freq: float, gain: float = 0.5, delay: float = 0.0,
              rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.12, 0.12))
        return Voice(osc="sweep", freq=freq * 1.8, freq_end=freq * 0.9,
                     attack=0.0001, decay_rate=350.0, attack_curve=3.0,
                     filt="bp", f_cutoff=freq * 0.8, f_high=freq * 1.8,
                     drive=2.0, gain=gain, delay=delay)

    @staticmethod
    def fm(freq: float, fm_idx: float = 0.4, gain: float = 0.35,
           cutoff: float = 3500, delay: float = 0.0,
           rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.08, 0.08))
        return Voice(osc="fm", freq=freq, fm_ratio=2.0, fm_index=fm_idx,
                     attack=0.0003, decay_rate=80.0, attack_curve=2.0,
                     filt="lp", f_cutoff=cutoff, drive=1.2, gain=gain, delay=delay)

    @staticmethod
    def housing(freq: float, gain: float = 0.30, delay: float = 0.0,
                rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.06, 0.06))
        return Voice(osc="modal",
                     modes=[(freq, 25.0, 1.0), (freq * 1.8, 40.0, 0.4), (freq * 2.5, 60.0, 0.2)],
                     attack=0.0008, decay_rate=0.0, attack_curve=1.5,
                     filt="lp", f_cutoff=2500, gain=gain, delay=delay)

    @staticmethod
    def thock(freq: float, gain: float = 0.45, delay: float = 0.002,
              rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.10, 0.10))
        return Voice(osc="sweep", freq=freq * 1.3, freq_end=freq * 0.85,
                     attack=0.0015, decay_rate=45.0, attack_curve=2.5,
                     filt="lp", f_cutoff=max(500.0, freq * 4.0), gain=gain, delay=delay)

    @staticmethod
    def sub(freq: float, gain: float = 0.30, delay: float = 0.003,
            rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.05, 0.05))
        return Voice(osc="sine", freq=freq, attack=0.002, decay_rate=30.0,
                     attack_curve=2.0, filt="lp", f_cutoff=250, gain=gain, delay=delay)

    @staticmethod
    def rattle(lo: float, hi: float, gain: float = 0.08, delay: float = 0.002) -> Voice:
        return Voice(osc="noise_white", attack=0.0005, decay_rate=100.0, attack_curve=1.0,
                     filt="bp", f_cutoff=lo, f_high=hi, drive=1.5, gain=gain, delay=delay)

    @staticmethod
    def spring(freq: float, gain: float = 0.4, delay: float = 0.0,
               rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.08, 0.08))
        mi = rng.uniform(0.8, 1.2) if rng else 1.0
        return Voice(osc="fm", freq=freq, fm_ratio=3.5, fm_index=mi,
                     attack=0.0002, decay_rate=12.0, attack_curve=1.5,
                     filt="lp", f_cutoff=12000, drive=1.0, gain=gain, delay=delay)

    @staticmethod
    def bell(freq: float, ratios: Sequence[Tuple[float, float]],
             gain: float = 0.50, decay: float = 4.0, inharmonicity: float = 0.0,
             rng: Optional[np.random.RandomState] = None) -> Voice:
        if rng:
            freq = freq * (2 ** rng.uniform(-0.03, 0.03))
        return Voice(osc="modal",
                     modes=[(freq * r, decay * (1 + i * 0.2), a) for i, (r, a) in enumerate(ratios)],
                     inharmonicity=inharmonicity, attack=0.0001, decay_rate=0.0,
                     attack_curve=1.0, filt="lp", f_cutoff=16000, gain=gain)


SOUND_PRESETS: Dict[str, Dict[str, str]] = {
    "Mechanical": {"desc": "Cherry MX Blue: sharp click jacket, tactile bump, deep housing resonance"},
    "Cherry MX Red": {"desc": "Linear thock: smooth POM stem, deep sub-bass, minimal high transient"},
    "Cherry MX Brown": {"desc": "Tactile bump: resonant mid-range friction with smooth decay"},
    "IBM Model M": {"desc": "Buckling spring: high-tension metallic ping, membrane snap, heavy housing"},
    "Logitech MX": {"desc": "Scissor switch: shallow, crisp, highly dampened plastic click"},
    "Typewriter": {"desc": "Heavy metal typebar strike with platen resonance and carriage bell"},
    "Cash Register": {"desc": "Mechanical key with drawer mechanism and classic ka-ching bell"},
    "Bubble Pop": {"desc": "Cavity resonance with pitch sweep and membrane rupture"},
    "Rain Drops": {"desc": "Water droplet modal synthesis with surface tension resonance"},
    "Membrane": {"desc": "Rubber dome collapse with muffled low-frequency resonance"},
    "Crystal": {"desc": "Inharmonic modal bell with stretched partials, long decay"},
    "Wooden": {"desc": "Marimba bar with odd-harmonic modes and resonator coupling"},
    "Soft Foam": {"desc": "Compressed foam thud with damped low-frequency resonance"},
    "Cat Paws": {"desc": "Soft pad impact with fur-damped transients"},
    "ASMR Deep Thock": {"desc": "Ultra-deep sub-bass thock with soft pink noise, optimized for brain tingles"},
    "ASMR Crisp Tactile": {"desc": "Sharp high-frequency transients mixed with crisp click for intense stereo imaging"},
    "ASMR Whisper": {"desc": "Breathy pink/brown noise combination for muted, soft typing"},
    "Rainy Cabin": {"desc": "Water droplet harmonics mixed with ambient rain noise for cozy atmosphere"},
    "ASMR Soft Rain": {"desc": "Very gentle rain droplets — sleep-friendly, low transient, soft resonance"},
}

CLICK_DURATIONS: Dict[str, float] = {
    "Mechanical": 0.12, "Cherry MX Red": 0.10, "Cherry MX Brown": 0.09,
    "IBM Model M": 0.25, "Logitech MX": 0.06, "Typewriter": 0.08,
    "Cash Register": 0.12, "Bubble Pop": 0.12, "Rain Drops": 0.10,
    "Membrane": 0.10, "Crystal": 0.40, "Wooden": 0.18, "Soft Foam": 0.18,
    "Cat Paws": 0.10, "ASMR Deep Thock": 0.18, "ASMR Crisp Tactile": 0.10,
    "ASMR Whisper": 0.12, "Rainy Cabin": 0.12, "ASMR Soft Rain": 0.12,
}

_VF = VoiceFactory

# ───────────────────────────────────────────────────────────────────
# MECHANICAL PRESETS
# ───────────────────────────────────────────────────────────────────

def _make_mechanical(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 4800 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.click(cf, 0.55, rng=rng),  # Sharp click jacket
         _VF.fm(1400 * (2 ** rng.uniform(-0.08, 0.08)), 0.45, 0.35, 4000, rng=rng),  # Tactile bump
         _VF.housing(420 * (2 ** rng.uniform(-0.06, 0.06)), 0.35, rng=rng),  # Housing resonance
         _VF.thock(160 * (2 ** rng.uniform(-0.10, 0.10)), 0.50, 0.002, rng=rng),  # Deep thock
         _VF.sub(85 * (2 ** rng.uniform(-0.05, 0.05)), 0.35, 0.003, rng=rng),  # Sub bass
         _VF.rattle(2200, 4500, 0.06, 0.002)]  # High rattle
    return DSP.to_int16(R.render(v, duration, rng))

def _make_mechanical_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 3500 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.click(cf, 0.45, rng=rng),
         _VF.fm(900 * (2 ** rng.uniform(-0.08, 0.08)), 0.35, 0.30, 3000, rng=rng),
         _VF.housing(320 * (2 ** rng.uniform(-0.06, 0.06)), 0.40, rng=rng),
         _VF.thock(130 * (2 ** rng.uniform(-0.10, 0.10)), 0.55, 0.002, rng=rng),
         _VF.sub(65 * (2 ** rng.uniform(-0.05, 0.05)), 0.40, 0.003, rng=rng),
         _VF.rattle(1800, 3500, 0.05, 0.002)]
    return DSP.to_int16(R.render(v, 0.10, rng))

def _make_mechanical_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 3000 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.click(cf, 0.50, rng=rng),
         _VF.fm(700 * (2 ** rng.uniform(-0.08, 0.08)), 0.35, 0.35, 3000, rng=rng),
         _VF.housing(280 * (2 ** rng.uniform(-0.06, 0.06)), 0.45, rng=rng),
         _VF.thock(110 * (2 ** rng.uniform(-0.10, 0.10)), 0.60, 0.002, rng=rng),
         _VF.sub(55 * (2 ** rng.uniform(-0.05, 0.05)), 0.45, 0.003, rng=rng),
         _VF.rattle(1500, 3000, 0.06, 0.002)]
    return DSP.to_int16(R.render(v, 0.11, rng))

def _make_red(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_white", attack=0.0004, decay_rate=220.0, attack_curve=2.0,
               filt="bp", f_cutoff=1800, f_high=4500, gain=0.18),  # POM stem friction
         _VF.housing(240 * (2 ** rng.uniform(-0.10, 0.10)), 0.40, rng=rng),
         _VF.thock(150 * (2 ** rng.uniform(-0.10, 0.10)), 0.55, 0.001, rng=rng),
         _VF.sub(110 * (2 ** rng.uniform(-0.05, 0.05)), 0.40, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_red_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_white", attack=0.0004, decay_rate=180.0, attack_curve=2.0,
               filt="bp", f_cutoff=1200, f_high=3500, gain=0.14),
         _VF.housing(150 * (2 ** rng.uniform(-0.10, 0.10)), 0.45, rng=rng),
         _VF.thock(110 * (2 ** rng.uniform(-0.10, 0.10)), 0.60, 0.001, rng=rng),
         _VF.sub(70 * (2 ** rng.uniform(-0.05, 0.05)), 0.45, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, 0.09, rng))

def _make_red_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_white", attack=0.0004, decay_rate=160.0, attack_curve=2.0,
               filt="bp", f_cutoff=1000, f_high=2500, gain=0.14),
         _VF.housing(120 * (2 ** rng.uniform(-0.10, 0.10)), 0.50, rng=rng),
         _VF.thock(95 * (2 ** rng.uniform(-0.10, 0.10)), 0.65, 0.001, rng=rng),
         _VF.sub(60 * (2 ** rng.uniform(-0.05, 0.05)), 0.50, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, 0.08, rng))

def _make_brown(sr=44100, duration=0.09, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_white", attack=0.0003, decay_rate=280.0, attack_curve=2.5,
               filt="bp", f_cutoff=2200, f_high=5000, gain=0.22),  # Tactile bump
         _VF.fm(550 * (2 ** rng.uniform(-0.08, 0.08)), 0.35, 0.30, 2500, rng=rng),
         _VF.housing(320 * (2 ** rng.uniform(-0.06, 0.06)), 0.40, rng=rng),
         _VF.thock(180 * (2 ** rng.uniform(-0.10, 0.10)), 0.50, 0.0015, rng=rng),
         _VF.sub(90 * (2 ** rng.uniform(-0.05, 0.05)), 0.35, 0.0025, rng=rng)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_brown_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_white", attack=0.0003, decay_rate=240.0, attack_curve=2.5,
               filt="bp", f_cutoff=1600, f_high=3800, gain=0.16),
         _VF.fm(400 * (2 ** rng.uniform(-0.08, 0.08)), 0.30, 0.25, 2000, rng=rng),
         _VF.housing(220 * (2 ** rng.uniform(-0.06, 0.06)), 0.45, rng=rng),
         _VF.thock(130 * (2 ** rng.uniform(-0.10, 0.10)), 0.55, 0.0015, rng=rng),
         _VF.sub(65 * (2 ** rng.uniform(-0.05, 0.05)), 0.40, 0.0025, rng=rng)]
    return DSP.to_int16(R.render(v, 0.07, rng))

def _make_brown_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_white", attack=0.0003, decay_rate=220.0, attack_curve=2.5,
               filt="bp", f_cutoff=1300, f_high=3200, gain=0.16),
         _VF.fm(300 * (2 ** rng.uniform(-0.08, 0.08)), 0.30, 0.30, 2000, rng=rng),
         _VF.housing(170 * (2 ** rng.uniform(-0.06, 0.06)), 0.50, rng=rng),
         _VF.thock(100 * (2 ** rng.uniform(-0.10, 0.10)), 0.60, 0.0015, rng=rng),
         _VF.sub(55 * (2 ** rng.uniform(-0.05, 0.05)), 0.45, 0.0025, rng=rng)]
    return DSP.to_int16(R.render(v, 0.07, rng))

# ───────────────────────────────────────────────────────────────────
# RETRO / NICHE PRESETS
# ───────────────────────────────────────────────────────────────────

def _make_ibm(sr=44100, duration=0.25, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    pf = 5200 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.spring(pf, 0.45, rng=rng),  # Buckling spring ping
         _VF.click(3200 * (2 ** rng.uniform(-0.10, 0.10)), 0.50, delay=0.001, rng=rng),  # Membrane
         _VF.housing(480 * (2 ** rng.uniform(-0.06, 0.06)), 0.35, delay=0.001, rng=rng),  # Heavy case
         Voice(osc="fm", freq=850 * (2 ** rng.uniform(-0.08, 0.08)), fm_ratio=1.5,
               fm_index=rng.uniform(0.3, 0.5), attack=0.0005, decay_rate=65.0,
               attack_curve=2.0, filt="lp", f_cutoff=4500, gain=0.28, delay=0.002),
         _VF.sub(130 * (2 ** rng.uniform(-0.05, 0.05)), 0.40, 0.002, rng=rng),
         Voice(osc="fm", freq=pf * 1.5, fm_ratio=2.7, fm_index=rng.uniform(0.7, 0.9),
               attack=0.0003, decay_rate=18.0, attack_curve=1.5, filt="lp",
               f_cutoff=14000, gain=0.25, delay=0.0005)]  # Spring tail
    return DSP.to_int16(R.render(v, duration, rng))

def _make_ibm_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    pf = 4800 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.spring(pf, 0.40, rng=rng),
         _VF.click(2600 * (2 ** rng.uniform(-0.10, 0.10)), 0.45, delay=0.001, rng=rng),
         _VF.housing(400 * (2 ** rng.uniform(-0.06, 0.06)), 0.40, delay=0.001, rng=rng),
         Voice(osc="fm", freq=650 * (2 ** rng.uniform(-0.08, 0.08)), fm_ratio=1.5,
               fm_index=rng.uniform(0.3, 0.5), attack=0.0005, decay_rate=55.0,
               attack_curve=2.0, filt="lp", f_cutoff=4000, gain=0.28, delay=0.002),
         _VF.sub(110 * (2 ** rng.uniform(-0.05, 0.05)), 0.45, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, 0.12, rng))

def _make_ibm_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    pf = 4500 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.spring(pf, 0.50, rng=rng),
         Voice(osc="fm", freq=pf * 1.3, fm_ratio=2.7, fm_index=rng.uniform(0.8, 1.0),
               attack=0.0003, decay_rate=16.0, attack_curve=1.5, filt="lp",
               f_cutoff=13000, gain=0.25, delay=0.0005),
         _VF.click(2300 * (2 ** rng.uniform(-0.10, 0.10)), 0.45, delay=0.001, rng=rng),
         _VF.housing(340 * (2 ** rng.uniform(-0.06, 0.06)), 0.45, delay=0.001, rng=rng),
         _VF.thock(110 * (2 ** rng.uniform(-0.10, 0.10)), 0.45, 0.002, rng=rng),
         _VF.sub(90 * (2 ** rng.uniform(-0.05, 0.05)), 0.45, 0.003, rng=rng)]
    return DSP.to_int16(R.render(v, 0.15, rng))

def _make_logi(sr=44100, duration=0.06, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 3000 * (2 ** rng.uniform(-0.12, 0.12))
    v = [_VF.click(cf, 0.50, rng=rng),  # Shallow click
         Voice(osc="sine", freq=1600 * (2 ** rng.uniform(-0.08, 0.08)), attack=0.0002,
               decay_rate=220.0, attack_curve=2.0, filt="lp", f_cutoff=6000, gain=0.28),
         Voice(osc="noise_white", attack=0.0001, decay_rate=500.0, attack_curve=2.0,
               filt="lp", f_cutoff=8000, gain=0.12, delay=0.0005)]  # Dampened crunch
    return DSP.to_int16(R.render(v, duration, rng))

def _make_logi_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2500 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.click(cf, 0.40, rng=rng),
         Voice(osc="sine", freq=1000 * (2 ** rng.uniform(-0.08, 0.08)), attack=0.0002,
               decay_rate=200.0, attack_curve=2.0, filt="lp", f_cutoff=5000, gain=0.28),
         Voice(osc="noise_white", attack=0.0001, decay_rate=450.0, attack_curve=2.0,
               filt="lp", f_cutoff=7000, gain=0.10, delay=0.0005)]
    return DSP.to_int16(R.render(v, 0.05, rng))

def _make_logi_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2200 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.click(cf, 0.42, rng=rng),
         Voice(osc="sine", freq=800 * (2 ** rng.uniform(-0.08, 0.08)), attack=0.0002,
               decay_rate=180.0, attack_curve=2.0, filt="lp", f_cutoff=4000, gain=0.30),
         Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=2.0,
               filt="lp", f_cutoff=6000, gain=0.12, delay=0.0005)]
    return DSP.to_int16(R.render(v, 0.05, rng))

def _make_typewriter(sr=44100, duration=0.08, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    sf = 4500 * (2 ** rng.uniform(-0.15, 0.15))
    v = [Voice(osc="noise_pink", attack=0.001, decay_rate=140.0, attack_curve=1.0,
               filt="bp", f_cutoff=500, f_high=2000, gain=0.22),  # Mechanism
         _VF.click(sf, 0.55, delay=0.002, rng=rng),  # Typebar strike
         Voice(osc="sine", freq=220 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.0005,
               decay_rate=65.0, attack_curve=2.0, filt="lp", f_cutoff=800, gain=0.40, delay=0.002),  # Platen
         Voice(osc="noise_white", attack=0.001, decay_rate=100.0, attack_curve=1.0,
               filt="bp", f_cutoff=1500, f_high=3500, gain=0.10, delay=0.003),
         _VF.housing(380 * (2 ** rng.uniform(-0.06, 0.06)), 0.30, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_typewriter_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    sf = 2000 * (2 ** rng.uniform(-0.12, 0.12))
    v = [Voice(osc="noise_pink", attack=0.001, decay_rate=110.0, attack_curve=1.0,
               filt="bp", f_cutoff=400, f_high=1500, gain=0.28),
         _VF.click(sf, 0.50, delay=0.002, rng=rng),
         Voice(osc="sine", freq=160 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.0005,
               decay_rate=55.0, attack_curve=2.0, filt="lp", f_cutoff=600, gain=0.45, delay=0.002),
         Voice(osc="noise_white", attack=0.001, decay_rate=80.0, attack_curve=1.0,
               filt="bp", f_cutoff=1000, f_high=2500, gain=0.12, delay=0.003)]
    return DSP.to_int16(R.render(v, 0.08, rng))

def _make_typewriter_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    slide = R.render([Voice(osc="noise_white", attack=0.005, decay_rate=20.0,
                            attack_curve=1.0, filt="bp", f_cutoff=200, f_high=800, gain=0.22),
                      Voice(osc="fm", freq=60, fm_ratio=8.0, fm_index=2.0,
                            attack=0.002, decay_rate=12.0, attack_curve=1.0,
                            filt="lp", f_cutoff=2000, gain=0.28)], 0.25, rng)
    bf = 2200 * (2 ** rng.uniform(-0.03, 0.03))
    bell = R.render([_VF.bell(bf, [(1.0, 1.0), (2.0, 0.5), (3.5, 0.3), (5.2, 0.2), (7.1, 0.1)],
                              gain=0.55, decay=4.0, inharmonicity=0.0001, rng=rng),
                     Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=2.0,
                           filt="bp", f_cutoff=bf * 0.7, f_high=bf * 1.3, drive=2.0, gain=0.15)], 0.40, rng)
    overlap = int(sr * 0.05)
    total = len(slide) + len(bell) - overlap
    out = np.zeros(total, dtype=np.float32)
    out[:len(slide)] += slide
    out[len(slide) - overlap:len(slide) - overlap + len(bell)] += bell
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_cashreg(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2800 * (2 ** rng.uniform(-0.12, 0.12))
    v = [_VF.click(cf, 0.55, rng=rng),
         Voice(osc="fm", freq=900 * (2 ** rng.uniform(-0.08, 0.08)), fm_ratio=1.5,
               fm_index=rng.uniform(0.4, 0.6), attack=0.0005, decay_rate=45.0,
               attack_curve=2.0, filt="lp", f_cutoff=4000, gain=0.35),  # Mechanism
         _VF.housing(320 * (2 ** rng.uniform(-0.06, 0.06)), 0.40, rng=rng),
         _VF.sub(110 * (2 ** rng.uniform(-0.05, 0.05)), 0.35, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_cashreg_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2000 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.click(cf, 0.50, rng=rng),
         Voice(osc="fm", freq=600 * (2 ** rng.uniform(-0.08, 0.08)), fm_ratio=1.5,
               fm_index=rng.uniform(0.3, 0.5), attack=0.0005, decay_rate=40.0,
               attack_curve=2.0, filt="lp", f_cutoff=3000, gain=0.35),
         _VF.housing(240 * (2 ** rng.uniform(-0.06, 0.06)), 0.45, rng=rng),
         _VF.sub(90 * (2 ** rng.uniform(-0.05, 0.05)), 0.40, 0.002, rng=rng)]
    return DSP.to_int16(R.render(v, 0.10, rng))

def _make_cashreg_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    press = R.render([_VF.click(1500 * (2 ** rng.uniform(-0.10, 0.10)), 0.45, rng=rng),
                      Voice(osc="sine", freq=100 * (2 ** rng.uniform(-0.08, 0.08)),
                            attack=0.001, decay_rate=150.0, attack_curve=2.0,
                            filt="lp", f_cutoff=500, gain=0.45)], 0.06, rng)
    ka = R.render([Voice(osc="fm", freq=850 * (2 ** rng.uniform(-0.08, 0.08)), fm_ratio=1.5,
                         fm_index=rng.uniform(0.4, 0.6), attack=0.001, decay_rate=20.0,
                         attack_curve=2.0, filt="lp", f_cutoff=10000, gain=0.40),
                   Voice(osc="noise_white", attack=0.0005, decay_rate=100.0, attack_curve=1.5,
                         filt="bp", f_cutoff=2000, f_high=6000, gain=0.18)], 0.18, rng)
    cf2 = 3500 * (2 ** rng.uniform(-0.03, 0.03))
    ching = R.render([_VF.bell(cf2, [(1.0, 1.0), (1.5, 0.6), (2.0, 0.4), (3.0, 0.2)],
                               gain=0.50, decay=3.0, rng=rng),
                      Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=2.0,
                            filt="bp", f_cutoff=cf2 * 0.7, f_high=cf2 * 1.3, drive=2.0, gain=0.12)], 0.40, rng)
    pause = int(sr * 0.04)
    total = len(press) + len(ka) + pause + len(ching)
    out = np.zeros(total, dtype=np.float32)
    out[:len(press)] += press
    off = len(press)
    out[off:off + len(ka)] += ka
    off += len(ka) + pause
    out[off:off + len(ching)] += ching
    return DSP.to_int16(DSP.normalize(out, -1.0))

# ───────────────────────────────────────────────────────────────────
# ORGANIC / SOFT PRESETS
# ───────────────────────────────────────────────────────────────────

def _make_bubble(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 800 * (2 ** rng.uniform(-0.20, 0.20))
    v = [Voice(osc="fm", freq=f0, fm_ratio=1.5, fm_index=rng.uniform(0.3, 0.5),
               attack=0.0005, decay_rate=25.0, attack_curve=3.0,
               filt="lp", f_cutoff=f0 * 3, gain=0.50),
         Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=2.0,
               filt="bp", f_cutoff=f0 * 0.5, f_high=f0 * 2, drive=1.5, gain=0.28),  # Membrane
         Voice(osc="sine", freq=f0 * 0.5, attack=0.001, decay_rate=30.0, attack_curve=2.0,
               filt="lp", f_cutoff=f0, gain=0.35)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_bubble_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 500 * (2 ** rng.uniform(-0.15, 0.15))
    v = [Voice(osc="fm", freq=f0, fm_ratio=1.5, fm_index=rng.uniform(0.3, 0.5),
               attack=0.0005, decay_rate=22.0, attack_curve=3.0,
               filt="lp", f_cutoff=f0 * 3, gain=0.50),
         Voice(osc="noise_white", attack=0.0001, decay_rate=250.0, attack_curve=2.0,
               filt="bp", f_cutoff=f0 * 0.5, f_high=f0 * 2, drive=1.5, gain=0.25),
         Voice(osc="sine", freq=f0 * 0.5, attack=0.001, decay_rate=25.0, attack_curve=2.0,
               filt="lp", f_cutoff=f0, gain=0.35)]
    return DSP.to_int16(R.render(v, 0.10, rng))

def _make_bubble_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.35); out = np.zeros(n, dtype=np.float32)
    for i in range(3):
        s = int(sr * i * 0.07)
        f0 = 700 + rng.randint(-150, 150) + i * 50
        pop = R.render([Voice(osc="fm", freq=f0, fm_ratio=1.5, fm_index=0.5,
                              attack=0.0005, decay_rate=25.0, attack_curve=3.0,
                              filt="lp", f_cutoff=f0 * 3, gain=0.50),
                       Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=2.0,
                             filt="bp", f_cutoff=f0 * 0.5, f_high=f0 * 2, drive=1.5, gain=0.22)], 0.08, rng)
        if s + len(pop) <= n:
            out[s:s + len(pop)] += pop
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_rain(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 3000 * (2 ** rng.uniform(-0.25, 0.25))
    v = [Voice(osc="noise_white", attack=0.0001, decay_rate=500.0, attack_curve=3.0,
               filt="bp", f_cutoff=f * 0.5, f_high=f * 1.5, drive=2.0, gain=0.45),
         Voice(osc="sine", freq=f, attack=0.0002, decay_rate=90.0, attack_curve=2.0,
               filt="resonator", f_cutoff=f, f_q=3.0, gain=0.40),
         Voice(osc="noise_pink", attack=0.001, decay_rate=70.0, attack_curve=1.5,
               filt="lp", f_cutoff=5000, gain=0.18, delay=0.002)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_rain_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 1800 * (2 ** rng.uniform(-0.20, 0.20))
    v = [Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=3.0,
               filt="bp", f_cutoff=f * 0.5, f_high=f * 1.5, drive=2.0, gain=0.40),
         Voice(osc="sine", freq=f, attack=0.0002, decay_rate=70.0, attack_curve=2.0,
               filt="resonator", f_cutoff=f, f_q=2.5, gain=0.40),
         Voice(osc="noise_pink", attack=0.001, decay_rate=60.0, attack_curve=1.5,
               filt="lp", f_cutoff=4000, gain=0.20, delay=0.002)]
    return DSP.to_int16(R.render(v, 0.07, rng))

def _make_rain_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.30); out = np.zeros(n, dtype=np.float32)
    for i in range(4):
        s = int(sr * (i * 0.06 + rng.uniform(0, 0.02)))
        f = 2500 + rng.randint(-500, 500)
        drop = R.render([Voice(osc="noise_white", attack=0.0001, decay_rate=500.0, attack_curve=3.0,
                               filt="bp", f_cutoff=f * 0.5, f_high=f * 1.5, drive=2.0, gain=0.40),
                        Voice(osc="sine", freq=f, attack=0.0002, decay_rate=80.0, attack_curve=2.0,
                              filt="resonator", f_cutoff=f, f_q=3.0, gain=0.35)], 0.05, rng)
        if s + len(drop) <= n:
            out[s:s + len(drop)] += drop
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_membrane(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=160 * (2 ** rng.uniform(-0.12, 0.12)), attack=0.005,
               decay_rate=45.0, attack_curve=1.5, filt="lp", f_cutoff=800, gain=0.55),
         Voice(osc="noise_white", attack=0.002, decay_rate=200.0, attack_curve=2.0,
               filt="lp", f_cutoff=2000, gain=0.12),
         Voice(osc="sine", freq=85 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.003,
               decay_rate=35.0, attack_curve=2.0, filt="lp", f_cutoff=300, gain=0.35, delay=0.001)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_membrane_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=110 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.006,
               decay_rate=40.0, attack_curve=1.5, filt="lp", f_cutoff=600, gain=0.60),
         Voice(osc="noise_white", attack=0.002, decay_rate=180.0, attack_curve=2.0,
               filt="lp", f_cutoff=1500, gain=0.10),
         Voice(osc="sine", freq=55 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.004,
               decay_rate=30.0, attack_curve=2.0, filt="lp", f_cutoff=200, gain=0.40, delay=0.001)]
    return DSP.to_int16(R.render(v, 0.09, rng))

def _make_membrane_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=95 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.006,
               decay_rate=38.0, attack_curve=1.5, filt="lp", f_cutoff=500, gain=0.60),
         Voice(osc="noise_white", attack=0.002, decay_rate=160.0, attack_curve=2.0,
               filt="lp", f_cutoff=1200, gain=0.10),
         Voice(osc="sine", freq=48 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.004,
               decay_rate=28.0, attack_curve=2.0, filt="lp", f_cutoff=180, gain=0.45, delay=0.001)]
    return DSP.to_int16(R.render(v, 0.08, rng))

def _make_crystal(sr=44100, duration=0.40, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 1500 * (2 ** rng.uniform(-0.12, 0.12))
    v = [_VF.bell(f0, [(1.0, 1.0), (2.1, 0.5), (3.3, 0.3), (4.7, 0.2), (6.1, 0.1)],
                  gain=0.55, decay=7.0, inharmonicity=0.0002, rng=rng),
         Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=3.0,
               filt="bp", f_cutoff=f0 * 0.7, f_high=f0 * 1.3, drive=2.0, gain=0.18)]
    return DSP.to_int16(R.render(v, duration, rng), target_db=-3.0)

def _make_crystal_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 900 * (2 ** rng.uniform(-0.10, 0.10))
    v = [_VF.bell(f0, [(1.0, 1.0), (2.1, 0.5), (3.3, 0.3), (4.7, 0.15)],
                  gain=0.55, decay=6.0, inharmonicity=0.0002, rng=rng),
         Voice(osc="noise_white", attack=0.0001, decay_rate=350.0, attack_curve=3.0,
               filt="bp", f_cutoff=f0 * 0.7, f_high=f0 * 1.3, drive=2.0, gain=0.14)]
    return DSP.to_int16(R.render(v, 0.25, rng), target_db=-3.0)

def _make_crystal_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.7); out = np.zeros(n, dtype=np.float32)
    for i, f0 in enumerate([2200, 2750, 3300]):
        s = int(sr * i * 0.12)
        f0 += rng.randint(-50, 50)
        chime = R.render([_VF.bell(f0, [(1.0, 1.0), (2.1, 0.5), (3.3, 0.3), (4.7, 0.2), (6.1, 0.1)],
                                   gain=0.50, decay=5.0, inharmonicity=0.0002, rng=rng),
                          Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=3.0,
                                filt="bp", f_cutoff=f0 * 0.7, f_high=f0 * 1.3, drive=2.0, gain=0.14)], 0.5, rng)
        if s + len(chime) <= n:
            out[s:s + len(chime)] += chime
    return DSP.to_int16(DSP.normalize(out, -3.0))

def _make_wooden(sr=44100, duration=0.18, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f1 = 600 * (2 ** rng.uniform(-0.12, 0.12))
    v = [Voice(osc="modal", modes=[(f1 * r, 40 * (1 + i * 0.3), a) for i, (r, a) in
                                   enumerate([(1.0, 1.0), (3.0, 0.4), (5.0, 0.2), (7.0, 0.1)])],
               attack=0.0005, decay_rate=0.0, attack_curve=2.0,
               filt="lp", f_cutoff=8000, gain=0.50),
         Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=3.0,
               filt="bp", f_cutoff=f1 * 0.5, f_high=f1 * 2, drive=1.5, gain=0.28),
         Voice(osc="sine", freq=f1 * 0.5, attack=0.001, decay_rate=30.0, attack_curve=2.0,
               filt="lp", f_cutoff=f1, gain=0.28)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_wooden_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f1 = 400 * (2 ** rng.uniform(-0.10, 0.10))
    v = [Voice(osc="modal", modes=[(f1 * r, 35 * (1 + i * 0.3), a) for i, (r, a) in
                                   enumerate([(1.0, 1.0), (3.0, 0.4), (5.0, 0.2)])],
               attack=0.0005, decay_rate=0.0, attack_curve=2.0,
               filt="lp", f_cutoff=7000, gain=0.50),
         Voice(osc="noise_white", attack=0.0001, decay_rate=280.0, attack_curve=3.0,
               filt="bp", f_cutoff=f1 * 0.5, f_high=f1 * 2, drive=1.5, gain=0.25),
         Voice(osc="sine", freq=f1 * 0.5, attack=0.001, decay_rate=28.0, attack_curve=2.0,
               filt="lp", f_cutoff=f1, gain=0.28)]
    return DSP.to_int16(R.render(v, 0.12, rng))

def _make_wooden_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.20); out = np.zeros(n, dtype=np.float32)
    for i in range(2):
        s = int(sr * i * 0.09)
        f1 = 350 + rng.randint(-50, 50)
        knock = R.render([Voice(osc="modal", modes=[(f1 * r, 40 * (1 + j * 0.3), a) for j, (r, a) in
                                                     enumerate([(1.0, 1.0), (3.0, 0.4), (5.0, 0.2)])],
                                attack=0.0005, decay_rate=0.0, attack_curve=2.0,
                                filt="lp", f_cutoff=7000, gain=0.45),
                          Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=3.0,
                                filt="bp", f_cutoff=f1 * 0.5, f_high=f1 * 2, drive=1.5, gain=0.25)], 0.08, rng)
        if s + len(knock) <= n:
            out[s:s + len(knock)] += knock
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_foam(sr=44100, duration=0.18, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=110 * (2 ** rng.uniform(-0.12, 0.12)), attack=0.01,
               decay_rate=22.0, attack_curve=1.5, filt="lp", f_cutoff=400, gain=0.55),
         Voice(osc="noise_brown", attack=0.008, decay_rate=25.0, attack_curve=1.5,
               filt="lp", f_cutoff=800, gain=0.35),
         Voice(osc="sine", freq=55 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.012,
               decay_rate=18.0, attack_curve=1.5, filt="lp", f_cutoff=150, gain=0.40, delay=0.002)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_foam_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=75 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.012,
               decay_rate=20.0, attack_curve=1.5, filt="lp", f_cutoff=300, gain=0.60),
         Voice(osc="noise_brown", attack=0.010, decay_rate=22.0, attack_curve=1.5,
               filt="lp", f_cutoff=600, gain=0.35),
         Voice(osc="sine", freq=38 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.014,
               decay_rate=15.0, attack_curve=1.5, filt="lp", f_cutoff=120, gain=0.40, delay=0.002)]
    return DSP.to_int16(R.render(v, 0.14, rng))

def _make_foam_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=65 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.012,
               decay_rate=18.0, attack_curve=1.5, filt="lp", f_cutoff=250, gain=0.60),
         Voice(osc="noise_brown", attack=0.010, decay_rate=20.0, attack_curve=1.5,
               filt="lp", f_cutoff=500, gain=0.35),
         Voice(osc="sine", freq=32 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.014,
               decay_rate=14.0, attack_curve=1.5, filt="lp", f_cutoff=100, gain=0.45, delay=0.002)]
    return DSP.to_int16(R.render(v, 0.12, rng))

def _make_catpaw(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=260 * (2 ** rng.uniform(-0.12, 0.12)), attack=0.002,
               decay_rate=70.0, attack_curve=2.5, filt="lp", f_cutoff=1500, gain=0.50),
         Voice(osc="noise_pink", attack=0.002, decay_rate=90.0, attack_curve=2.0,
               filt="lp", f_cutoff=2000, gain=0.22),
         Voice(osc="sine", freq=125 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.003,
               decay_rate=50.0, attack_curve=2.0, filt="lp", f_cutoff=500, gain=0.35, delay=0.001)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_catpaw_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="sine", freq=190 * (2 ** rng.uniform(-0.10, 0.10)), attack=0.002,
               decay_rate=60.0, attack_curve=2.5, filt="lp", f_cutoff=1200, gain=0.50),
         Voice(osc="noise_pink", attack=0.002, decay_rate=80.0, attack_curve=2.0,
               filt="lp", f_cutoff=1500, gain=0.18),
         Voice(osc="sine", freq=95 * (2 ** rng.uniform(-0.05, 0.05)), attack=0.003,
               decay_rate=45.0, attack_curve=2.0, filt="lp", f_cutoff=400, gain=0.35, delay=0.001)]
    return DSP.to_int16(R.render(v, 0.08, rng))

def _make_catpaw_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.15); out = np.zeros(n, dtype=np.float32)
    for i in range(2):
        s = int(sr * i * 0.06)
        paw = R.render([Voice(osc="sine", freq=230 * (2 ** rng.uniform(-0.08, 0.08)), attack=0.002,
                              decay_rate=70.0, attack_curve=2.5, filt="lp", f_cutoff=1500, gain=0.45),
                       Voice(osc="noise_pink", attack=0.002, decay_rate=90.0, attack_curve=2.0,
                             filt="lp", f_cutoff=2000, gain=0.18)], 0.06, rng)
        if s + len(paw) <= n:
            out[s:s + len(paw)] += paw
    return DSP.to_int16(DSP.normalize(out, -1.0))

# ───────────────────────────────────────────────────────────────────
# ASMR OPTIMIZED PRESETS
# ───────────────────────────────────────────────────────────────────

def _make_asmr_thock(sr=44100, duration=0.18, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 110 * (2 ** rng.uniform(-0.04, 0.04))
    v = [_VF.thock(f, gain=0.75, delay=0.001, rng=rng),
         _VF.sub(f * 0.55, gain=0.55, delay=0.002, rng=rng),
         Voice(osc="noise_pink", attack=0.006, decay_rate=45.0, attack_curve=2.0,
               filt="lp", f_cutoff=900, gain=0.18),
         _VF.housing(f * 2.2, gain=0.22, delay=0.003, rng=rng),
         Voice(osc="sine", freq=f * 1.5, attack=0.002, decay_rate=22.0, attack_curve=2.5,
               filt="lp", f_cutoff=800, gain=0.12, delay=0.004)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_asmr_thock_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 85 * (2 ** rng.uniform(-0.04, 0.04))
    v = [_VF.thock(f, gain=0.80, delay=0.001, rng=rng),
         _VF.sub(f * 0.5, gain=0.60, delay=0.002, rng=rng),
         Voice(osc="noise_pink", attack=0.006, decay_rate=38.0, attack_curve=2.0,
               filt="lp", f_cutoff=700, gain=0.20)]
    return DSP.to_int16(R.render(v, 0.14, rng))

def _make_asmr_thock_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 65 * (2 ** rng.uniform(-0.04, 0.04))
    v = [_VF.thock(f, gain=0.85, delay=0.001, rng=rng),
         _VF.sub(f * 0.5, gain=0.65, delay=0.002, rng=rng),
         Voice(osc="noise_pink", attack=0.006, decay_rate=32.0, attack_curve=2.0,
               filt="lp", f_cutoff=600, gain=0.22),
         Voice(osc="sine", freq=f * 1.4, attack=0.003, decay_rate=18.0, attack_curve=2.5,
               filt="lp", f_cutoff=700, gain=0.15, delay=0.004)]
    return DSP.to_int16(R.render(v, 0.18, rng))

def _make_asmr_crisp(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 3600 * (2 ** rng.uniform(-0.04, 0.04))
    v = [Voice(osc="noise_white", attack=0.0003, decay_rate=220.0, attack_curve=1.5,
               filt="bp", f_cutoff=f * 0.8, f_high=f * 1.5, drive=1.4, gain=0.28),
         _VF.click(f, gain=0.45, rng=rng),
         Voice(osc="sine", freq=320 * (2 ** rng.uniform(-0.04, 0.04)), attack=0.0008,
               decay_rate=70.0, attack_curve=2.0, filt="lp", f_cutoff=2200, gain=0.30),
         Voice(osc="noise_pink", attack=0.002, decay_rate=60.0, attack_curve=2.0,
               filt="lp", f_cutoff=2500, gain=0.10, delay=0.001)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_asmr_crisp_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 2600 * (2 ** rng.uniform(-0.04, 0.04))
    v = [Voice(osc="noise_white", attack=0.0003, decay_rate=180.0, attack_curve=1.5,
               filt="bp", f_cutoff=f * 0.8, f_high=f * 1.5, drive=1.4, gain=0.24),
         _VF.click(f, gain=0.40, rng=rng),
         Voice(osc="sine", freq=240 * (2 ** rng.uniform(-0.04, 0.04)), attack=0.0008,
               decay_rate=62.0, attack_curve=2.0, filt="lp", f_cutoff=1800, gain=0.30)]
    return DSP.to_int16(R.render(v, 0.09, rng))

def _make_asmr_crisp_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 2000 * (2 ** rng.uniform(-0.04, 0.04))
    v = [Voice(osc="noise_white", attack=0.0003, decay_rate=160.0, attack_curve=1.5,
               filt="bp", f_cutoff=f * 0.8, f_high=f * 1.5, drive=1.4, gain=0.24),
         _VF.click(f, gain=0.40, rng=rng),
         Voice(osc="sine", freq=200 * (2 ** rng.uniform(-0.04, 0.04)), attack=0.0008,
               decay_rate=55.0, attack_curve=2.0, filt="lp", f_cutoff=1500, gain=0.35),
         Voice(osc="noise_pink", attack=0.002, decay_rate=40.0, attack_curve=2.0,
               filt="lp", f_cutoff=1500, gain=0.10, delay=0.001)]
    return DSP.to_int16(R.render(v, 0.11, rng))

def _make_asmr_whisper(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_pink", attack=0.010, decay_rate=35.0, attack_curve=3.0,
               filt="bp", f_cutoff=1800, f_high=5500, gain=0.35),
         Voice(osc="noise_brown", attack=0.006, decay_rate=30.0, attack_curve=2.0,
               filt="lp", f_cutoff=400, gain=0.25),
         Voice(osc="noise_white", attack=0.0005, decay_rate=300.0, attack_curve=2.0,
               filt="hp", f_cutoff=6000, drive=1.2, gain=0.06)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_asmr_whisper_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_pink", attack=0.012, decay_rate=30.0, attack_curve=3.0,
               filt="bp", f_cutoff=1500, f_high=5000, gain=0.32),
         Voice(osc="noise_brown", attack=0.008, decay_rate=28.0, attack_curve=2.0,
               filt="lp", f_cutoff=350, gain=0.28)]
    return DSP.to_int16(R.render(v, 0.11, rng))

def _make_asmr_whisper_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    v = [Voice(osc="noise_pink", attack=0.012, decay_rate=28.0, attack_curve=3.0,
               filt="bp", f_cutoff=1200, f_high=4500, gain=0.35),
         Voice(osc="noise_brown", attack=0.008, decay_rate=24.0, attack_curve=2.0,
               filt="lp", f_cutoff=300, gain=0.30)]
    return DSP.to_int16(R.render(v, 0.14, rng))

def _make_asmr_rainy(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 2500 * (2 ** rng.uniform(-0.15, 0.15))
    v = [Voice(osc="noise_white", attack=0.0002, decay_rate=300.0, attack_curve=2.0,
               filt="bp", f_cutoff=f * 0.5, f_high=f * 1.5, gain=0.28),
         Voice(osc="sine", freq=f * 0.5, attack=0.001, decay_rate=60.0, attack_curve=2.0,
               filt="lp", f_cutoff=f, gain=0.35),
         Voice(osc="noise_pink", attack=0.005, decay_rate=50.0, attack_curve=1.5,
               filt="bp", f_cutoff=1000, f_high=3000, gain=0.18, delay=0.002)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_asmr_rainy_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 1500 * (2 ** rng.uniform(-0.15, 0.15))
    v = [Voice(osc="noise_white", attack=0.0002, decay_rate=250.0, attack_curve=2.0,
               filt="bp", f_cutoff=f * 0.5, f_high=f * 1.5, gain=0.25),
         Voice(osc="sine", freq=f * 0.5, attack=0.001, decay_rate=50.0, attack_curve=2.0,
               filt="lp", f_cutoff=f, gain=0.32),
         Voice(osc="noise_pink", attack=0.005, decay_rate=40.0, attack_curve=1.5,
               filt="bp", f_cutoff=800, f_high=2500, gain=0.20, delay=0.002)]
    return DSP.to_int16(R.render(v, 0.10, rng))

def _make_asmr_rainy_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.20); out = np.zeros(n, dtype=np.float32)
    for i in range(3):
        s = int(sr * i * 0.05)
        f = 2000 + rng.randint(-400, 400)
        drop = R.render([Voice(osc="noise_white", attack=0.0002, decay_rate=250.0, attack_curve=2.0,
                                filt="bp", f_cutoff=f * 0.5, f_high=f * 1.5, gain=0.22),
                         Voice(osc="sine", freq=f * 0.5, attack=0.001, decay_rate=50.0, attack_curve=2.0,
                               filt="lp", f_cutoff=f, gain=0.28)], 0.06, rng)
        if s + len(drop) <= n:
            out[s:s + len(drop)] += drop
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_asmr_soft_rain(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 1800 * (2 ** rng.uniform(-0.15, 0.15))
    v = [Voice(osc="noise_white", attack=0.0015, decay_rate=180.0, attack_curve=2.5,
               filt="bp", f_cutoff=f * 0.3, f_high=f * 0.8, drive=1.2, gain=0.24),
         Voice(osc="sine", freq=f, attack=0.0025, decay_rate=40.0, attack_curve=2.5,
               filt="resonator", f_cutoff=f, f_q=1.5, gain=0.24),
         Voice(osc="noise_pink", attack=0.003, decay_rate=28.0, attack_curve=2.0,
               filt="lp", f_cutoff=3000, gain=0.16, delay=0.002)]
    return DSP.to_int16(R.render(v, duration, rng))

def _make_asmr_soft_rain_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 1200 * (2 ** rng.uniform(-0.15, 0.15))
    v = [Voice(osc="noise_white", attack=0.0015, decay_rate=160.0, attack_curve=2.5,
               filt="bp", f_cutoff=f * 0.3, f_high=f * 0.8, drive=1.2, gain=0.22),
         Voice(osc="sine", freq=f, attack=0.0025, decay_rate=35.0, attack_curve=2.5,
               filt="resonator", f_cutoff=f, f_q=1.5, gain=0.22),
         Voice(osc="noise_pink", attack=0.003, decay_rate=25.0, attack_curve=2.0,
               filt="lp", f_cutoff=2500, gain=0.16, delay=0.002)]
    return DSP.to_int16(R.render(v, 0.10, rng))

def _make_asmr_soft_rain_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.20); out = np.zeros(n, dtype=np.float32)
    for i in range(3):
        s = int(sr * i * 0.05)
        f = 1500 + rng.randint(-300, 300)
        drop = R.render([Voice(osc="noise_white", attack=0.0015, decay_rate=160.0, attack_curve=2.5,
                                filt="bp", f_cutoff=f * 0.3, f_high=f * 0.8, drive=1.2, gain=0.20),
                         Voice(osc="sine", freq=f, attack=0.0025, decay_rate=35.0, attack_curve=2.5,
                               filt="resonator", f_cutoff=f, f_q=1.5, gain=0.22),
                         Voice(osc="noise_pink", attack=0.003, decay_rate=25.0, attack_curve=2.0,
                               filt="lp", f_cutoff=2500, gain=0.14)], 0.06, rng)
        if s + len(drop) <= n:
            out[s:s + len(drop)] += drop
    return DSP.to_int16(DSP.normalize(out, -1.0))


_PRESET_FACTORIES: Dict[str, Dict[str, Callable]] = {
    "Mechanical": {"click": _make_mechanical, "space": _make_mechanical_space, "enter": _make_mechanical_enter},
    "Cherry MX Red": {"click": _make_red, "space": _make_red_space, "enter": _make_red_enter},
    "Cherry MX Brown": {"click": _make_brown, "space": _make_brown_space, "enter": _make_brown_enter},
    "IBM Model M": {"click": _make_ibm, "space": _make_ibm_space, "enter": _make_ibm_enter},
    "Logitech MX": {"click": _make_logi, "space": _make_logi_space, "enter": _make_logi_enter},
    "Typewriter": {"click": _make_typewriter, "space": _make_typewriter_space, "enter": _make_typewriter_enter},
    "Cash Register": {"click": _make_cashreg, "space": _make_cashreg_space, "enter": _make_cashreg_enter},
    "Bubble Pop": {"click": _make_bubble, "space": _make_bubble_space, "enter": _make_bubble_enter},
    "Rain Drops": {"click": _make_rain, "space": _make_rain_space, "enter": _make_rain_enter},
    "Membrane": {"click": _make_membrane, "space": _make_membrane_space, "enter": _make_membrane_enter},
    "Crystal": {"click": _make_crystal, "space": _make_crystal_space, "enter": _make_crystal_enter},
    "Wooden": {"click": _make_wooden, "space": _make_wooden_space, "enter": _make_wooden_enter},
    "Soft Foam": {"click": _make_foam, "space": _make_foam_space, "enter": _make_foam_enter},
    "Cat Paws": {"click": _make_catpaw, "space": _make_catpaw_space, "enter": _make_catpaw_enter},
    "ASMR Deep Thock": {"click": _make_asmr_thock, "space": _make_asmr_thock_space, "enter": _make_asmr_thock_enter},
    "ASMR Crisp Tactile": {"click": _make_asmr_crisp, "space": _make_asmr_crisp_space, "enter": _make_asmr_crisp_enter},
    "ASMR Whisper": {"click": _make_asmr_whisper, "space": _make_asmr_whisper_space, "enter": _make_asmr_whisper_enter},
    "Rainy Cabin": {"click": _make_asmr_rainy, "space": _make_asmr_rainy_space, "enter": _make_asmr_rainy_enter},
    "ASMR Soft Rain": {"click": _make_asmr_soft_rain, "space": _make_asmr_soft_rain_space, "enter": _make_asmr_soft_rain_enter},
}


class SimpleSoundGen:
    __slots__ = ("sr", "preset", "stereo", "reverb_amt", "key_sounds", "mod_sounds",
                 "spaces", "enters", "releases", "backspaces", "fallback_clicks", "_ir_l", "_ir_r")
    
    _SHIFT_MAP = {
        '~': '`', '!': '1', '@': '2', '#': '3', '$': '4', '%': '5', '^': '6',
        '&': '7', '*': '8', '(': '9', ')': '0', '_': '-', '+': '=', '{': '[',
        '}': ']', '|': '\\', ':': ';', '"': "'", '<': ',', '>': '.', '?': '/'
    }

    def __init__(self, sr: int = 44100, preset: str = "Mechanical",
                 stereo: bool = False, reverb_amt: float = 0.1):
        self.sr, self.preset, self.stereo, self.reverb_amt = sr, preset, stereo, reverb_amt
        factories = _PRESET_FACTORIES.get(preset, _PRESET_FACTORIES["Mechanical"])
        click_dur = CLICK_DURATIONS.get(preset, 0.06)

        # Pre-generate distinct sounds per physical key with ASMR-optimized pitch shifting
        self.key_sounds = {}
        seed_base = 0

        # Row 1 (Numbers/Symbols) - 1.10x (Crisp but smoothed so it's not piercing)
        for ch in "`1234567890-=[]\\":
            snd = factories["click"](sr, duration=click_dur, seed=seed_base)
            self.key_sounds[ch.lower()] = self._pitch_shift(snd, 1.10, sr)
            seed_base += 1

        # Row 2 (QWERTY) - 1.04x (Slightly elevated, natural typing position)
        for ch in "qwertyuiop":
            snd = factories["click"](sr, duration=click_dur, seed=seed_base)
            self.key_sounds[ch.lower()] = self._pitch_shift(snd, 1.04, sr)
            seed_base += 1

        # Row 3 (ASDF) - 0.98x (Neutral, warm middle)
        for ch in "asdfghjkl;'":
            snd = factories["click"](sr, duration=click_dur, seed=seed_base)
            self.key_sounds[ch.lower()] = self._pitch_shift(snd, 0.98, sr)
            seed_base += 1

        # Row 4 (ZXCV) - 0.92x (Deep thock, triggers ASMR tingles)
        for ch in "zxcvbnm,./":
            snd = factories["click"](sr, duration=click_dur, seed=seed_base)
            self.key_sounds[ch.lower()] = self._pitch_shift(snd, 0.92, sr)
            seed_base += 1

        # Modifiers (Tab, Shift, Caps, etc.) - 0.88x (Large, heavy, deep)
        self.mod_sounds = {}
        mod_seed = 500
        for mod_name in ["tab", "caps", "shift", "ctrl", "alt", "win", "fn", "menu", "esc"]:
            snd = factories["space"](sr, seed=mod_seed)
            self.mod_sounds[mod_name] = self._pitch_shift(snd, 0.88, sr)
            mod_seed += 1

        self.fallback_clicks = [factories["click"](sr, duration=click_dur, seed=900 + i) for i in range(8)]
        # Space (0.85x) & Enter (0.86x) are very deep to emphasize the large key travel
        self.spaces = [self._pitch_shift(factories["space"](sr, seed=600 + i), 0.85, sr) for i in range(3)]
        self.enters = [self._pitch_shift(factories["enter"](sr, seed=700 + i), 0.86, sr) for i in range(2)]
        self.backspaces = [self._pitch_shift(self._make_backspace_tick(sr, seed=800 + i), 0.88, sr) for i in range(2)]
        self.releases = [self._make_release_tick(sr, seed=300 + i) for i in range(8)]

        self._ir_l = self._ir_r = None
        if self.reverb_amt > 0:
            self._get_reverb_ir()

    @staticmethod
    def _pitch_shift(sample: np.ndarray, mult: float, sr: int = 44100) -> np.ndarray:
        """ASMR-friendly pitch shifting: anti-aliasing for highs, sub-bass boost for lows."""
        if mult == 1.0 or len(sample) == 0:
            return sample
            
        s = sample.astype(np.float32) / 32767.0
        
        # 1. Anti-aliasing: Low-pass before pitching UP to prevent harsh digital noise
        if mult > 1.0:
            cutoff = min(8500, (sr / 2.0 / mult) * 0.9)
            s = DSP.filt_lp(s, cutoff, sr, n_taps=63)
            
        n = len(s)
        new_n = max(1, int(n / mult))
        indices = np.linspace(0, n - 1, new_n)
        left = np.floor(indices).astype(int)
        right = np.minimum(left + 1, n - 1)
        frac = indices - left
        shifted = s[left] * (1 - frac) + s[right] * frac
        
        # 2. Sub-warmth: Pitching DOWN can sound muffled. High-pass the mud and boost 40-120Hz for ASMR chest-feel
        if mult < 1.0:
            shifted = DSP.filt_hp(shifted, 30.0, sr, n_taps=63)  # Cut sub-rumble
            sub = DSP.filt_bp(shifted, 40, 120, sr, n_taps=127)  # Isolate sub-bass
            shifted = shifted + sub * 0.25  # Boost it back for a satisfying thock
            
        return np.clip(shifted * 32767, -32768, 32767).astype(np.int16)

    def _make_release_tick(self, sr: int = 44100, seed: int = 0) -> np.ndarray:
        rng = np.random.RandomState(seed); R = SoundRenderer(sr)
        v = [Voice(osc="noise_white", attack=0.0001, decay_rate=600.0, attack_curve=2.0,
                   filt="hp", f_cutoff=5000, drive=1.5, gain=0.18),
             Voice(osc="sine", freq=4200 * (2 ** rng.uniform(-0.15, 0.15)), attack=0.0001,
                   decay_rate=350.0, attack_curve=1.5, gain=0.08),
             Voice(osc="sweep", freq=6000, freq_end=3000, attack=0.00005, decay_rate=800.0,
                   attack_curve=2.0, filt="bp", f_cutoff=4000, f_high=8000, gain=0.05, delay=0.0002)]
        return DSP.to_int16(R.render(v, 0.035, rng))

    def _make_backspace_tick(self, sr: int = 44100, seed: int = 0) -> np.ndarray:
        rng = np.random.RandomState(seed); R = SoundRenderer(sr)
        v = [Voice(osc="sweep", freq=250, freq_end=120, attack=0.001, decay_rate=70.0,
                   attack_curve=2.0, filt="lp", f_cutoff=500, gain=0.35),
             Voice(osc="noise_white", attack=0.0002, decay_rate=250.0, attack_curve=2.0,
                   filt="bp", f_cutoff=1200, f_high=3000, gain=0.12)]
        return DSP.to_int16(R.render(v, 0.05, rng))

    def _get_reverb_ir(self) -> Tuple[np.ndarray, np.ndarray]:
        needs_long = self.reverb_amt > 0.2
        if (self._ir_l is None) or ((len(self._ir_l) > 44100) != needs_long):
            sr = self.sr; n = int(sr * (1.5 if needs_long else 0.8))
            rng = np.random.RandomState(42); t = np.arange(n, dtype=np.float32) / sr
            ir_l, ir_r = np.zeros(n, dtype=np.float32), np.zeros(n, dtype=np.float32)
            for i, (dt, g) in enumerate(zip(np.linspace(0.005, 0.080, 40), np.linspace(0.8, 0.1, 40))):
                ds = int(dt * sr)
                if ds < n:
                    if i % 2 == 0:
                        ir_l[ds] += g * (1.0 if rng.rand() > 0.5 else -1.0)
                        ir_r[min(ds + int(0.002 * sr), n - 1)] += g * 0.5 * (1.0 if rng.rand() > 0.5 else -1.0)
                    else:
                        ir_r[ds] += g * (1.0 if rng.rand() > 0.5 else -1.0)
                        ir_l[min(ds + int(0.0015 * sr), n - 1)] += g * 0.5 * (1.0 if rng.rand() > 0.5 else -1.0)
            tail_l, tail_r = np.zeros(n, dtype=np.float32), np.zeros(n, dtype=np.float32)
            for f, p, d in zip(rng.uniform(30, 600, 80), rng.uniform(0, 2 * np.pi, 80), rng.uniform(1.5, 4.5, 80)):
                wave = np.sin(2 * np.pi * f * t + p) * np.exp(-t * d)
                tail_l += wave * rng.uniform(0.6, 1.4)
                tail_r += wave * rng.uniform(0.6, 1.4)
            ir_l += tail_l * 0.02 + rng.randn(n).astype(np.float32) * np.exp(-t * 6.0) * 0.06
            ir_r += tail_r * 0.02 + rng.randn(n).astype(np.float32) * np.exp(-t * 6.0) * 0.06
            if np.max(np.abs(ir_l)) > 0: ir_l /= np.max(np.abs(ir_l))
            if np.max(np.abs(ir_r)) > 0: ir_r /= np.max(np.abs(ir_r))
            ir_l = DSP.filt_hp(DSP.filt_lp(ir_l, 7000, sr, n_taps=127), 150, sr, n_taps=63)
            ir_r = DSP.filt_hp(DSP.filt_lp(ir_r, 7000, sr, n_taps=127), 150, sr, n_taps=63)
            pd = int(sr * 0.012)
            self._ir_l = np.concatenate([np.zeros(pd, dtype=np.float32), ir_l])[:n]
            self._ir_r = np.concatenate([np.zeros(pd, dtype=np.float32), ir_r])[:n]
        return self._ir_l, self._ir_r

    def _pick(self, char: str, rng: random.Random) -> Tuple[np.ndarray, float]:
        if char == "__release__":
            return rng.choice(self.releases), rng.uniform(0.4, 0.6)
        if char == "\b":
            return rng.choice(self.backspaces), rng.uniform(0.85, 1.0)
        if char == "\n":
            return rng.choice(self.enters), rng.uniform(1.10, 1.25)
        if char == " ":
            return self.spaces[rng.randint(0, 2)], rng.uniform(1.05, 1.15)
        if char == "\t":
            return self.mod_sounds["tab"], rng.uniform(0.95, 1.05)

        cl = char.lower()
        if cl in self._SHIFT_MAP:
            cl = self._SHIFT_MAP[cl]

        if cl in self.key_sounds:
            return self.key_sounds[cl], rng.uniform(0.92, 1.08)

        return rng.choice(self.fallback_clicks), rng.uniform(0.92, 1.08)

    def _generate_ambient(self, n: int, rng: np.random.RandomState,
                         intensity: float = 1.0, sr: int = 44100) -> np.ndarray:
        bed = DSP.noise_pink(n, rng, sr).astype(np.float32) * 0.0005 * intensity
        deep = DSP.noise_brown(n, rng).astype(np.float32) * 0.0008 * intensity
        lfo = 0.5 + 0.5 * np.sin(2 * np.pi * 0.05 * (np.arange(n, dtype=np.float32) / sr))
        return (bed + deep * lfo).astype(np.float32)

    def generate_pcm(self, timestamps: List[Tuple[float, str]],
                     volume: float = 0.5) -> np.ndarray:
        if not timestamps:
            return np.zeros(0, dtype=np.int16)
        sr = self.sr; rng = random.Random(98765); all_ts: List[Tuple[float, str]] = []
        for ts, ch in timestamps:
            all_ts.append((ts, ch))
            if ch.isalnum() or ch in ".,;[]'":
                all_ts.append((ts + 0.045 + rng.uniform(0, 0.015), "__release__"))
        n = int(sr * (max(ts for ts, _ in all_ts) + 0.3))
        raw_sounds: List[Tuple[np.ndarray, float, int]] = []
        for ts, ch in all_ts:
            snd, vm = self._pick(ch, rng)
            s = int(ts * sr)
            if s >= n:
                continue
            snd_float = snd.astype(np.float32) / 32767.0
            if len(snd_float) == 0:
                continue
            vv = rng.gauss(1.0, 0.05) * vm
            snd_mono = snd_float * (vv ** 0.8)
            if vv > 1.05:
                snd_mono = np.tanh(snd_mono * (1.0 + (vv - 1.0) * 2.5)) / np.tanh(1.0 + (vv - 1.0) * 2.5)
            snd_mono *= volume
            pan = 0.0
            if self.stereo:
                cl = ch.lower()
                if cl in self._SHIFT_MAP: cl = self._SHIFT_MAP[cl]
                if cl in "qazwsx12345edcrfv tgbyhn":
                    pan = rng.uniform(-0.7, -0.3)
                elif cl in "yp[]\\=-7890uio phjklnm,./;'":
                    pan = rng.uniform(0.3, 0.7)
                elif ch in (" ", "\n", "\t"):
                    pan = rng.uniform(-0.1, 0.1)
                else:
                    pan = rng.uniform(-0.3, 0.3)
            raw_sounds.append((snd_mono, pan, s))

        if not raw_sounds:
            return np.zeros(n, dtype=np.int16)

        if self.stereo:
            max_len = n + int(0.001 * sr)
            mix_l, mix_r = np.zeros(max_len, dtype=np.float32), np.zeros(max_len, dtype=np.float32)
            for snd_mono, pan, s in raw_sounds:
                l_sig, r_sig = DSP.binaural_pan(snd_mono, pan, sr)
                e = min(s + len(l_sig), max_len)
                mix_l[s:e] += l_sig[:e - s]
                mix_r[s:e] += r_sig[:e - s]
            mix_l += self._generate_ambient(max_len, np.random.RandomState(123), 1.0, sr)
            mix_r += self._generate_ambient(max_len, np.random.RandomState(456), 1.0, sr)
            if self.reverb_amt > 0:
                ir_l, ir_r = self._get_reverb_ir()
                rev_l = DSP.convolve(mix_l, ir_l)[:max_len]
                rev_r = DSP.convolve(mix_r, ir_r)[:max_len]
                np.multiply(mix_l, (1.0 - self.reverb_amt), out=mix_l)
                np.multiply(rev_l, self.reverb_amt, out=rev_l)
                np.add(mix_l, rev_l, out=mix_l)
                np.multiply(mix_r, (1.0 - self.reverb_amt), out=mix_r)
                np.multiply(rev_r, self.reverb_amt, out=rev_r)
                np.add(mix_r, rev_r, out=mix_r)
            mix_l, mix_r = mix_l[:n], mix_r[:n]
            mix_l, mix_r = DSP.master_stereo_asmr(mix_l, mix_r, sr)
            np.nan_to_num(mix_l, copy=False, nan=0.0, posinf=1.0, neginf=-1.0)
            np.nan_to_num(mix_r, copy=False, nan=0.0, posinf=1.0, neginf=-1.0)
            out = np.empty(n * 2, dtype=np.int16)
            out[0::2] = np.clip(mix_l * 32767, -32768, 32767).astype(np.int16)
            out[1::2] = np.clip(mix_r * 32767, -32768, 32767).astype(np.int16)
            return out

        mono_sounds = [s[0] for s in raw_sounds]
        starts = np.array([s[2] for s in raw_sounds], dtype=np.int64)
        lengths = np.array([len(s) for s in mono_sounds], dtype=np.int64)
        flat = np.concatenate(mono_sounds) if mono_sounds else np.array([], dtype=np.float32)
        offsets = np.zeros(len(mono_sounds), dtype=np.int64)
        for i in range(1, len(mono_sounds)):
            offsets[i] = offsets[i - 1] + lengths[i - 1]
        mix = np.zeros(n, dtype=np.float32)
        if len(flat) > 0:
            if _HAS_NUMBA:
                _nb_mix(mix, flat, offsets, lengths, starts)
            else:
                for i in range(len(starts)):
                    s_idx, ln, o = int(starts[i]), int(lengths[i]), int(offsets[i])
                    mix[s_idx:s_idx + ln] += flat[o:o + ln]
        mix += self._generate_ambient(n, np.random.RandomState(123), 1.0, sr)
        if self.reverb_amt > 0:
            ir_l, ir_r = self._get_reverb_ir()
            rev = DSP.convolve(mix, (ir_l + ir_r) * 0.5)[:n]
            mix = mix * (1.0 - self.reverb_amt) + rev * self.reverb_amt
        mix = DSP.master_mono(mix, sr)
        np.nan_to_num(mix, copy=False, nan=0.0, posinf=1.0, neginf=-1.0)
        return np.clip(mix * 32767.0, -32768, 32767).astype(np.int16)

    def generate_track(self, timestamps: List[Tuple[float, str]],
                       filepath: str, volume: float = 0.5) -> None:
        if not timestamps:
            return
        pcm = self.generate_pcm(timestamps, volume)
        if len(pcm) == 0:
            return
        with wave.open(filepath, "w") as wf:
            wf.setnchannels(2 if self.stereo else 1)
            wf.setsampwidth(2)
            wf.setframerate(self.sr)
            wf.writeframes(pcm.astype('<i2').tobytes())


def _pcm_to_wav_bytes(pcm: np.ndarray, sr: int = 44100, channels: int = 1) -> bytes:
    buf = io.BytesIO()
    with wave.open(buf, "w") as wf:
        wf.setnchannels(channels)
        wf.setsampwidth(2)
        wf.setframerate(sr)
        wf.writeframes(pcm.tobytes())
    return buf.getvalue()


# ═══════════════════════════════════════════════════════════════════
# SECTION 8 — KEYBOARD LAYOUTS & OVERLAY
# ═══════════════════════════════════════════════════════════════════

_US_SHIFT: Dict[str, str] = {
    "~": "`", "!": "1", "@": "2", "#": "3", "$": "4", "%": "5", "^": "6",
    "&": "7", "*": "8", "(": "9", ")": "0", "_": "-", "+": "=", "{": "[",
    "}": "]", "|": "\\", ":": ";", '"': "'", "<": ",", ">": ".", "?": "/",
}

_QWERTY_ROWS = [
    [("`", 1), ("1", 1), ("2", 1), ("3", 1), ("4", 1), ("5", 1), ("6", 1), ("7", 1), ("8", 1), ("9", 1), ("0", 1), ("-", 1), ("=", 1), ("Bksp", 2)],
    [("Tab", 1.5), ("Q", 1), ("W", 1), ("E", 1), ("R", 1), ("T", 1), ("Y", 1), ("U", 1), ("I", 1), ("O", 1), ("P", 1), ("[", 1), ("]", 1), ("\\", 1.5)],
    [("Caps", 1.75), ("A", 1), ("S", 1), ("D", 1), ("F", 1), ("G", 1), ("H", 1), ("J", 1), ("K", 1), ("L", 1), (";", 1), ("'", 1), ("Enter", 2.25)],
    [("Shift", 2.25), ("Z", 1), ("X", 1), ("C", 1), ("V", 1), ("B", 1), ("N", 1), ("M", 1), (",", 1), (".", 1), ("/", 1), ("Shift", 2.75)],
    [("Ctrl", 1.25), ("Win", 1.25), ("Alt", 1.25), ("", 6.25), ("Alt", 1.25), ("Fn", 1.25), ("Menu", 1.25), ("Ctrl", 1.25)],
]
_DVORAK_ROWS = [
    [("`", 1), ("1", 1), ("2", 1), ("3", 1), ("4", 1), ("5", 1), ("6", 1), ("7", 1), ("8", 1), ("9", 1), ("0", 1), ("[", 1), ("]", 1), ("Bksp", 2)],
    [("Tab", 1.5), ("'", 1), (",", 1), (".", 1), ("P", 1), ("Y", 1), ("F", 1), ("G", 1), ("C", 1), ("R", 1), ("L", 1), ("/", 1), ("=", 1), ("\\", 1.5)],
    [("Caps", 1.75), ("A", 1), ("O", 1), ("E", 1), ("U", 1), ("I", 1), ("D", 1), ("H", 1), ("T", 1), ("N", 1), ("S", 1), ("-", 1), ("Enter", 2.25)],
    [("Shift", 2.25), (";", 1), ("Q", 1), ("J", 1), ("K", 1), ("X", 1), ("B", 1), ("M", 1), ("W", 1), ("V", 1), ("Z", 1), ("Shift", 2.75)],
    [("Ctrl", 1.25), ("Win", 1.25), ("Alt", 1.25), ("", 6.25), ("Alt", 1.25), ("Fn", 1.25), ("Menu", 1.25), ("Ctrl", 1.25)],
]
_COLEMAK_ROWS = [
    [("`", 1), ("1", 1), ("2", 1), ("3", 1), ("4", 1), ("5", 1), ("6", 1), ("7", 1), ("8", 1), ("9", 1), ("0", 1), ("-", 1), ("=", 1), ("Bksp", 2)],
    [("Tab", 1.5), ("Q", 1), ("W", 1), ("F", 1), ("P", 1), ("G", 1), ("J", 1), ("L", 1), ("U", 1), ("Y", 1), (";", 1), ("[", 1), ("]", 1), ("\\", 1.5)],
    [("Bksp", 1.75), ("A", 1), ("R", 1), ("S", 1), ("T", 1), ("D", 1), ("H", 1), ("N", 1), ("E", 1), ("I", 1), ("O", 1), ("'", 1), ("Enter", 2.25)],
    [("Shift", 2.25), ("Z", 1), ("X", 1), ("C", 1), ("V", 1), ("B", 1), ("K", 1), ("M", 1), (",", 1), (".", 1), ("/", 1), ("Shift", 2.75)],
    [("Ctrl", 1.25), ("Win", 1.25), ("Alt", 1.25), ("", 6.25), ("Alt", 1.25), ("Fn", 1.25), ("Menu", 1.25), ("Ctrl", 1.25)],
]

KEYBOARD_LAYOUTS: Dict[str, Dict] = {
    "QWERTY": {"description": "Standard US QWERTY layout", "rows": _QWERTY_ROWS, "shift_map": _US_SHIFT},
    "Dvorak": {"description": "Dvorak ergonomic layout", "rows": _DVORAK_ROWS, "shift_map": _US_SHIFT},
    "Colemak": {"description": "Colemak ergonomic layout", "rows": _COLEMAK_ROWS, "shift_map": _US_SHIFT},
}


def _build_char_map(layout_name: str) -> Dict[str, Tuple[int, int]]:
    ld = KEYBOARD_LAYOUTS[layout_name]; cm: Dict[str, Tuple[int, int]] = {}
    for ri, row in enumerate(ld["rows"]):
        for ci, (label, w) in enumerate(row):
            ll = label.lower()
            if len(label) == 1:
                cm[label] = cm[ll] = cm[label.upper()] = (ri, ci)
            if ll == "space" or (label == "" and w >= 4):
                cm[" "] = (ri, ci)
            elif "enter" in ll:
                cm["\n"] = (ri, ci)
            elif "tab" in ll:
                cm["\t"] = (ri, ci)
            elif "bksp" in ll:
                cm["\x08"] = (ri, ci)
    for shifted, base in ld.get("shift_map", {}).items():
        if base in cm:
            cm[shifted] = cm[base]
    return cm


class KeyboardOverlay:
    __slots__ = ("video_w", "video_h", "layout_name", "theme", "opacity",
                 "rows", "char_map", "num_rows", "position", "key_unit",
                 "key_gap", "key_h", "_max_units", "_max_keys", "_kb_width",
                 "_kb_height", "_kb_x", "_kb_y", "key_rects", "_bg_cache")

    def __init__(self, video_w: int, video_h: int, layout_name: str = "QWERTY",
                 theme: Optional[Dict[str, str]] = None, opacity: float = 0.82,
                 max_height: Optional[int] = None,
                 position: str = "bottom_center"):
        self.video_w = video_w
        self.video_h = video_h
        self.layout_name = layout_name
        self.theme = theme or THEMES["Dracula"]
        self.opacity = opacity
        self.rows = KEYBOARD_LAYOUTS[layout_name]["rows"]
        self.char_map = _build_char_map(layout_name)
        self.num_rows = len(self.rows)
        self.position = position
        self.key_unit = max(20, int(video_w * 0.028))
        self.key_gap = max(2, self.key_unit // 14)
        self.key_h = int(self.key_unit * 0.82)

        if max_height and max_height > 0:
            natural_h = self.num_rows * self.key_h + (self.num_rows - 1) * self.key_gap
            if natural_h > max_height:
                lo, hi = 10, self.key_unit
                for _ in range(30):
                    mid = (lo + hi) / 2
                    tg = max(2, int(mid) // 14)
                    th = self.num_rows * int(mid * 0.82) + (self.num_rows - 1) * tg
                    if th > max_height:
                        hi = mid
                    else:
                        lo = mid
                self.key_unit = max(10, int(lo))
                self.key_gap = max(2, self.key_unit // 14)
                self.key_h = int(self.key_unit * 0.82)

        self._max_units = max(sum(w for _, w in row) for row in self.rows)
        self._max_keys = max(len(row) for row in self.rows)
        self._kb_width = int(self._max_units * self.key_unit + (self._max_keys - 1) * self.key_gap)
        self._kb_height = int(len(self.rows) * self.key_h + (len(self.rows) - 1) * self.key_gap)
        self._kb_x = (video_w - self._kb_width) // 2
        self._kb_y = video_h - self._kb_height - max(8, video_h // 60)
        self._apply_position()
        self.key_rects: Dict[Tuple[int, int], QRect] = {}
        self._rebuild_key_rects()
        self._bg_cache: Optional[QImage] = None
        self._build_bg_cache()

    def height_needed(self) -> int:
        return self._kb_height + max(8, self.video_h // 60) + max(6, self.video_h // 90)

    def _apply_position(self) -> None:
        m = max(8, self.video_h // 60)
        vw, vh, kw, kh = self.video_w, self.video_h, self._kb_width, self._kb_height
        pos = self.position
        match pos:
            case "bottom_center":
                self._kb_x, self._kb_y = (vw - kw) // 2, vh - kh - m
            case "bottom_right":
                self._kb_x, self._kb_y = vw - kw - m, vh - kh - m
            case "bottom_left":
                self._kb_x, self._kb_y = m, vh - kh - m
            case "top_center":
                self._kb_x, self._kb_y = (vw - kw) // 2, m
            case "top_right":
                self._kb_x, self._kb_y = vw - kw - m, m
            case "top_left":
                self._kb_x, self._kb_y = m, m
            case "center_left":
                self._kb_x, self._kb_y = m, (vh - kh) // 2
            case "center_right":
                self._kb_x, self._kb_y = vw - kw - m, (vh - kh) // 2

    def _rebuild_key_rects(self) -> None:
        self.key_rects = {}
        for ri, row in enumerate(self.rows):
            x = self._kb_x
            for ci, (_, w) in enumerate(row):
                kw = int(w * self.key_unit) - self.key_gap
                y = self._kb_y + ri * (self.key_h + self.key_gap)
                self.key_rects[(ri, ci)] = QRect(x, y, kw, self.key_h)
                x += int(w * self.key_unit)
        self._bg_cache = None

    def reposition(self, y_below: int = 0) -> None:
        self._apply_position()
        self._rebuild_key_rects()

    def resolve_key(self, ch: str) -> Optional[Tuple[int, int]]:
        return self.char_map.get(ch)

    def _build_bg_cache(self) -> None:
        pad = max(6, self.key_unit // 4)
        w = self._kb_width + 2 * pad
        h = self._kb_height + 2 * pad
        self._bg_cache = QImage(w, h, QImage.Format_ARGB32_Premultiplied)
        self._bg_cache.fill(Qt.transparent)
        p = QPainter(self._bg_cache)
        p.setRenderHint(QPainter.Antialiasing)
        th = self.theme or THEMES["Dracula"]
        radius = max(3, self.key_unit // 8)
        p.setPen(QPen(QColor(th["window_border"]), max(1, self.key_unit // 20)))
        p.setBrush(QColor(th["background"]))
        p.drawRoundedRect(0, 0, w, h, radius * 2, radius * 2)
        p.setFont(QFont("Arial", max(7, int(self.key_unit * 0.30))))
        for (ri, ci), rect in self.key_rects.items():
            label = self.rows[ri][ci][0]
            cache_rect = QRect(rect.x() - self._kb_x + pad, rect.y() - self._kb_y + pad,
                               rect.width(), rect.height())
            p.setBrush(QColor(th["title_bar"]))
            p.setPen(QColor(th["window_border"]))
            p.drawRoundedRect(cache_rect, radius, radius)
            if label:
                is_mod = len(label) > 1
                p.setPen(QColor(th["line_number"] if is_mod else th.get("foreground", "#f8f8f2")))
                p.drawText(cache_rect, Qt.AlignCenter, label)
        p.end()

    def draw(self, painter: QPainter, active_key: Optional[Tuple[int, int]] = None,
             flash: float = 0.0) -> None:
        painter.save()
        painter.setOpacity(self.opacity)
        if self._bg_cache is None:
            self._build_bg_cache()
        pad = max(6, self.key_unit // 4)
        painter.drawImage(self._kb_x - pad, self._kb_y - pad, self._bg_cache)
        if flash > 0 and active_key is not None:
            th = self.theme or THEMES["Dracula"]
            try:
                hl_base = QColor(th["cursor"])
            except KeyError:
                hl_base = QColor("#89b4fa")
            key_bg = QColor(th["title_bar"])
            flash_eased = 1.0 - (1.0 - flash) ** 2
            hl_fill = QColor(
                int(key_bg.red() + (hl_base.red() - key_bg.red()) * flash_eased),
                int(key_bg.green() + (hl_base.green() - key_bg.green()) * flash_eased),
                int(key_bg.blue() + (hl_base.blue() - key_bg.blue()) * flash_eased),
            )
            hl_glow = QColor(hl_base)
            hl_glow.setAlpha(int(60 * flash_eased))
            hl_expand = max(3, int(self.key_unit * 0.12 * flash_eased))
            rect = self.key_rects[active_key]
            radius = max(3, self.key_unit // 8)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(hl_glow)
            painter.drawRoundedRect(rect.adjusted(-hl_expand, -hl_expand, hl_expand, hl_expand),
                                    radius, radius)
            painter.setBrush(hl_fill)
            painter.setPen(QColor(th["window_border"]))
            painter.drawRoundedRect(rect, radius, radius)
            label = self.rows[active_key[0]][active_key[1]][0]
            if label:
                is_mod = len(label) > 1
                painter.setPen(QColor(th["line_number"] if is_mod else th.get("foreground", "#f8f8f2")))
                painter.setFont(QFont("Arial", max(7, int(self.key_unit * 0.30))))
                painter.drawText(rect, Qt.AlignCenter, label)
        painter.restore()


# ═══════════════════════════════════════════════════════════════════
# SECTION 9 — TYPING ANIMATION ENGINE
# ═══════════════════════════════════════════════════════════════════

Event = Tuple[float, int, str]

_QWERTY_POS: Dict[str, Tuple[int, int]] = {}
for _r, _row in enumerate(("`1234567890-=", "qwertyuiop[]\\", "asdfghjkl;'", "zxcvbnm,./")):
    for _c, _ch in enumerate(_row):
        _QWERTY_POS[_ch] = (_r, _c)
for _ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
    _QWERTY_POS[_ch] = _QWERTY_POS.get(_ch.lower(), (2, 0))

_QWERTY_NEARBY: Dict[str, str] = {
    'a': 'qwsz', 'b': 'vghn', 'c': 'xdfv', 'd': 'serfcx', 'e': 'wrsdf',
    'f': 'drtgvc', 'g': 'ftyhbv', 'h': 'gyujnb', 'i': 'ujklo', 'j': 'huikmn',
    'k': 'jilpm', 'l': 'kop', 'm': 'njk', 'n': 'bhjm', 'o': 'iklp', 'p': 'ol',
    'q': 'wa', 'r': 'edft', 's': 'awedz', 't': 'rfgy', 'u': 'yhji', 'v': 'cfgb',
    'w': 'qasde', 'x': 'zsdc', 'y': 'tghu', 'z': 'asx', ' ': ' ',
}


class TypingProfileBuilder:
    def __init__(self):
        self._name = "junior"
        self._wpm = 90
        self._pause_freq = 0.15
        self._burst_chance = 0.15
        self._start_pause = 0.5
        self._end_pause = 1.5
        self._auto_indent = True
        self._error_chance = 0.03

    def name(self, n: str) -> "TypingProfileBuilder":
        self._name = n; return self
    def wpm(self, w: int) -> "TypingProfileBuilder":
        self._wpm = w; return self
    def pause_freq(self, p: float) -> "TypingProfileBuilder":
        self._pause_freq = p; return self
    def burst_chance(self, b: float) -> "TypingProfileBuilder":
        self._burst_chance = b; return self
    def start_pause(self, s: float) -> "TypingProfileBuilder":
        self._start_pause = s; return self
    def end_pause(self, e: float) -> "TypingProfileBuilder":
        self._end_pause = e; return self
    def auto_indent(self, a: bool) -> "TypingProfileBuilder":
        self._auto_indent = a; return self
    def error_chance(self, e: float) -> "TypingProfileBuilder":
        self._error_chance = e; return self

    def build(self) -> "TypingProfile":
        return TypingProfile(
            name=self._name, wpm=self._wpm, pause_freq=self._pause_freq,
            burst_chance=self._burst_chance, start_pause=self._start_pause,
            end_pause=self._end_pause, auto_indent=self._auto_indent,
            error_chance=self._error_chance,
        )


@dataclass(slots=True)
class TypingProfile:
    name: str = "junior"
    wpm: int = 90
    pause_freq: float = 0.15
    burst_chance: float = 0.15
    start_pause: float = 0.5
    end_pause: float = 1.5
    auto_indent: bool = True
    error_chance: float = 0.03

    @classmethod
    def builder(cls) -> TypingProfileBuilder:
        return TypingProfileBuilder()


class TypingAnimator:
    __slots__ = ("code", "profile", "base_delay", "display_chars",
                 "text_snapshots", "error_snapshots", "timeline", "_timestamps")

    def __init__(self, code: str, profile: TypingProfile, seed: Optional[int] = None):
        self.code = code
        self.profile = profile
        self.base_delay = 1.0 / ((profile.wpm * 5) / 60)
        self.display_chars: List[str] = []
        self.text_snapshots: List[str] = []
        self.error_snapshots: List[List[bool]] = []
        self.timeline: List[Event] = self._build(seed if seed is not None else 42)
        self._timestamps = [ts for ts, _, _ in self.timeline]

    def _get_typo(self, ch: str, rng: random.Random) -> str:
        lower = ch.lower()
        if lower in _QWERTY_NEARBY:
            typo = rng.choice(_QWERTY_NEARBY[lower])
            return typo.upper() if ch.isupper() else typo
        return ch

    def _build(self, seed: int) -> List[Event]:
        rng = random.Random(seed)
        t = self.profile.start_pause
        events: List[Event] = []
        p = self.profile
        i = 0
        current_text: List[str] = []
        current_errors: List[bool] = []
        self.text_snapshots.append("")
        self.error_snapshots.append([])

        def take_snapshot():
            self.text_snapshots.append("".join(current_text))
            self.error_snapshots.append(list(current_errors))

        while i < len(self.code):
            ch = self.code[i]
            d = self.base_delay * rng.uniform(0.6, 1.4)

            match ch:
                case "\n": d *= rng.uniform(2.0, 4.0)
                case " ": d *= rng.uniform(0.7, 1.3)
                case "\t": d *= rng.uniform(1.2, 1.8)
                case _:
                    if ch in "([{":
                        d *= rng.uniform(1.1, 1.8)
                    elif ch in ")]}":
                        d *= rng.uniform(0.9, 1.5)
                    elif ch in ",;:":
                        d *= rng.uniform(1.3, 2.2)

            if i >= 1:
                pa = _QWERTY_POS.get(self.code[i - 1].lower())
                pb = _QWERTY_POS.get(ch.lower())
                if pa and pb:
                    dist = math.hypot(pa[0] - pb[0], pa[1] - pb[1])
                    if dist < 0.5:
                        d *= 0.7
                    elif dist > 4:
                        d *= 1.15

            if ch == ":" and i > 0:
                if "def " in self.code[max(0, i - 10):i] or "class " in self.code[max(0, i - 10):i]:
                    if rng.random() < 0.6:
                        d += rng.uniform(2.0, 5.0)
            elif ch == ":":
                if rng.random() < 0.2:
                    d += rng.uniform(1.0, 2.5)

            if ch in ("\n", ":"):
                if rng.random() < p.pause_freq:
                    d += rng.uniform(0.4, 1.2)
            elif rng.random() < (p.pause_freq * 0.2):
                d += rng.uniform(0.3, 0.8)

            if rng.random() < 0.012:
                d += rng.uniform(0.4, 1.4)

            if ch.isalpha() and rng.random() < p.error_chance and i + 1 < len(self.code):
                typo_ch = self._get_typo(ch, rng)
                if typo_ch != ch:
                    current_text.append(typo_ch)
                    current_errors.append(True)
                    self.display_chars.append(typo_ch)
                    events.append((t, len(self.display_chars) - 1, typo_ch))
                    take_snapshot()
                    t += max(d * 0.5, 0.012) + rng.uniform(0.05, 0.15)
                    current_text.append("\b")
                    current_errors.append(False)
                    self.display_chars.append("\b")
                    events.append((t, len(self.display_chars) - 1, "\b"))
                    take_snapshot()
                    t += max(d * 0.3, 0.008)

            burst_active = False
            if ch.isalpha() and rng.random() < p.burst_chance and i + 1 < len(self.code):
                burst_len = rng.randint(4, 9)
                burst_chars = []
                for bi in range(burst_len):
                    if i + bi >= len(self.code):
                        break
                    bc = self.code[i + bi]
                    burst_chars.append(bc)
                    current_text.append(bc)
                    current_errors.append(False)
                    self.display_chars.append(bc)
                    events.append((t, len(self.display_chars) - 1, bc))
                    take_snapshot()
                    t += max(d * 0.25, 0.012)
                i += len(burst_chars)
                t += rng.uniform(0.05, 0.15)
                burst_active = True

            if not burst_active:
                current_text.append(ch)
                current_errors.append(False)
                self.display_chars.append(ch)
                events.append((t, len(self.display_chars) - 1, ch))
                take_snapshot()
                t += max(d, 0.012)
                i += 1

            if p.auto_indent and ch == "\n" and i < len(self.code):
                indent = ""
                while i < len(self.code) and self.code[i] in (' ', '\t'):
                    indent += self.code[i]
                    i += 1
                if indent:
                    for ind_ch in indent:
                        current_text.append(ind_ch)
                        current_errors.append(False)
                        self.display_chars.append(ind_ch)
                        events.append((t, len(self.display_chars) - 1, ind_ch))
                        take_snapshot()
                        t += max(d * 0.3, 0.008)
        return events

    def duration(self) -> float:
        return (self.timeline[-1][0] + self.profile.end_pause
                if self.timeline else self.profile.start_pause + self.profile.end_pause)

    def visible_at(self, t: float) -> int:
        if t < self.profile.start_pause:
            return 0
        idx = bisect.bisect_right(self._timestamps, t)
        return self.timeline[idx - 1][1] + 1 if idx > 0 else 0

    def char_timestamps(self) -> List[Tuple[float, str]]:
        return [(ts, ch) for ts, _, ch in self.timeline if ch != "\b"]

    def active_key_at(self, t: float, flash_duration: float = 0.18
                      ) -> Tuple[Optional[str], float]:
        if not self._timestamps:
            return (None, 0.0)
        idx = bisect.bisect_right(self._timestamps, t)
        if idx == 0:
            return (None, 0.0)
        char = self.timeline[idx - 1][2]
        dt = t - self.timeline[idx - 1][0]
        return (char, max(0.0, 1.0 - dt / flash_duration)) if dt < flash_duration else (None, 0.0)


# ═══════════════════════════════════════════════════════════════════
# SECTION 10 — CODE RENDERING
# ═══════════════════════════════════════════════════════════════════

class CodeRenderer:
    TOKEN_COLOR_MAP: Final[Dict[str, str]] = {
        "keyword": "keyword", "builtin": "builtin", "string": "string",
        "number": "number", "comment": "comment", "decorator": "decorator",
        "function": "function", "class_name": "class_name", "operator": "operator",
        "boolean": "number", "constant": "number", "preprocessor": "decorator",
        "variable": "function", "symbol": "string", "macro": "function",
        "tag": "keyword", "attr": "builtin", "selector": "keyword",
        "property": "builtin", "value": "string", "hex_color": "number",
        "heading": "keyword", "bold": "keyword", "italic": "keyword",
        "code": "string", "link": "function", "punctuation": "comment",
        "fstring": "string", "lifetime": "constant", "annotation": "decorator",
    }
    CURSOR_BLINK: Final[float] = 0.53

    def __init__(self, width: int, height: int, theme_name: str = "Dracula",
                 font_family: str = "Consolas", font_size: int = 22,
                 show_line_numbers: bool = True, show_window_chrome: bool = True,
                 padding: int = 24, tab_size: int = 4, title_text: str = "main.py",
                 language: str = "Python", keyboard_overlay: Optional[KeyboardOverlay] = None,
                 bg_image_path: Optional[str] = None, total_code_lines: int = 0,
                 cursor_glow: bool = True, show_watermark: bool = False,
                 accent_color: Optional[str] = None):
        self.width = width
        self.height = height
        self.theme = THEMES.get(theme_name, THEMES["Dracula"])
        self.theme_name = theme_name
        self.font_family = font_family
        self.font_size = font_size
        self.show_line_numbers = show_line_numbers
        self.show_window_chrome = show_window_chrome
        self.padding = padding
        self.tab_size = tab_size
        self.title_text = title_text
        self.language = language
        self.keyboard_overlay = keyboard_overlay
        self.total_code_lines = total_code_lines
        self.cursor_glow = cursor_glow
        self.show_watermark = show_watermark
        self.accent_color = accent_color or self.theme.get("junior_accent", "#7aa2f7")

        _families = [font_family, "JetBrains Mono", "DejaVu Sans Mono",
                     "Liberation Mono", "Courier New", "monospace"]
        _available = QFontDatabase.families()
        chosen = "monospace"
        for f in _families:
            if f in _available:
                chosen = f
                break
        self.font = QFont(chosen, font_size)
        self.font.setFamilies(_families)
        self.font.setFixedPitch(True)
        self.fm = QFontMetrics(self.font)
        self.char_w = self.fm.horizontalAdvance("M")
        self.line_h = self.fm.height()
        self._qcolors = {k: QColor(v) for k, v in self.theme.items()
                         if isinstance(v, str) and v.startswith("#")}
        self._qc_fg = self._qcolors.get("foreground", QColor("#f8f8f2"))
        self._qc_ln = self._qcolors.get("line_number", QColor("#6272a4"))
        self._qc_ln_active = QColor(self._qc_fg).darker(120)
        self._qc_cursor = self._qcolors.get("cursor", QColor("#f8f8f2"))
        self._qc_current_line = self._qcolors.get("current_line", QColor("#44475a"))
        self._qc_accent = QColor(self.accent_color)
        self.bg_image = (QImage(bg_image_path) if bg_image_path
                         and os.path.exists(bg_image_path) else None)
        self._build_bg_cache()
        self._layout_nv: Union[str, int] = -1
        self._layout_lines: List[str] = []
        self._layout_offsets: List[int] = []
        self._layout_cursor_line: int = 0
        self._line_cache: "OrderedDict[str, List[int]]" = OrderedDict()
        self._tab_advance = self.char_w * self.tab_size
        self._tok_cache: "OrderedDict[str, List[str]]" = OrderedDict()

    @staticmethod
    def auto_font_size(code_lines: int, width: int, height: int,
                       padding: int = 24, show_chrome: bool = True,
                       show_ln: bool = True, tab_size: int = 4,
                       code: Optional[str] = None,
                       font_family: str = "Consolas",
                       keyboard_h: int = 0) -> int:
        chrome_h = 42 if show_chrome else 0
        kb_used = min(keyboard_h, (height - 2 * padding) // 3) if keyboard_h > 0 else 0
        rect_h = height - 2 * padding - kb_used - chrome_h
        rect_w = width - 2 * padding - 8
        if rect_h < 20 or rect_w < 40 or code_lines < 1:
            return 14
        max_chars = 80
        if code:
            longest = max(len(line.replace("\t", " " * tab_size)) for line in code.split("\n"))
            max_chars = max(longest, 1)

        def _ln_w(cw: int) -> int:
            return (len(str(code_lines)) * cw + 16) if show_ln else 0

        max_font = max(14, min(48, int(width / 80)))
        target_vis = min(code_lines, 35)
        max_check = min(max_chars, 120)
        lo, hi, best = 8, max_font, 14
        while lo <= hi:
            mid = (lo + hi) // 2
            fm = QFontMetrics(QFont(font_family, mid))
            lh = fm.height()
            if target_vis * lh <= rect_h:
                cw = fm.horizontalAdvance("M")
                if max_check * cw + _ln_w(cw) <= rect_w:
                    best = mid
                    lo = mid + 1
                else:
                    hi = mid - 1
            else:
                hi = mid - 1
        return max(8, best)

    def _get_line_layout(self, line: str) -> List[int]:
        cached = self._line_cache.get(line)
        if cached is not None:
            return cached
        char_x: List[int] = []
        x = 0
        tab = self._tab_advance
        ham = self.fm.horizontalAdvance
        for ch in line:
            char_x.append(x)
            x += tab if ch == "\t" else ham(ch)
        if len(self._line_cache) >= 512:
            self._line_cache.popitem(last=False)
        self._line_cache[line] = char_x
        return char_x

    def _tokenize_to_colors(self, text: str) -> List[str]:
        cached = self._tok_cache.get(text)
        if cached is not None:
            return cached
        tokens = Tokenizer.tokenize(text, self.language)
        colors = ["foreground"] * len(text)
        pos = 0
        get = self.TOKEN_COLOR_MAP.get
        n = len(colors)
        for ttype, ttxt in tokens:
            ckey = get(ttype, "foreground")
            end = min(pos + len(ttxt), n)
            colors[pos:end] = [ckey] * (end - pos)
            pos = end
        if len(self._tok_cache) > 256:
            self._tok_cache.popitem(last=False)
        self._tok_cache[text] = colors
        return colors

    def _build_bg_cache(self) -> None:
        self._bg = QImage(self.width, self.height, QImage.Format_RGB32)
        self._bg.fill(QColor(self.theme["background"]))
        p = QPainter(self._bg)
        p.setRenderHint(QPainter.Antialiasing)
        if self.bg_image:
            scaled = self.bg_image.scaled(
                self.width, self.height,
                Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                Qt.TransformationMode.SmoothTransformation,
            )
            p.drawImage((self.width - scaled.width()) // 2,
                        (self.height - scaled.height()) // 2, scaled)
            p.fillRect(0, 0, self.width, self.height, QColor(0, 0, 0, 130))
        else:
            bg = self._qcolors.get("background", QColor("#282a36"))
            g = QLinearGradient(0, 0, 0, self.height)
            g.setColorAt(0, bg.lighter(105))
            g.setColorAt(1, bg)
            p.fillRect(0, 0, self.width, self.height, g)
        w, h, pad = self.width, self.height, self.padding
        chrome_h = 42 if self.show_window_chrome else 0
        kb_reserve = (min(self.keyboard_overlay.height_needed(), (h - 2 * pad) // 3)
                     if self.keyboard_overlay else 0)
        wx, wy, ww, wh = pad, pad, w - 2 * pad, h - 2 * pad - kb_reserve
        p.setPen(Qt.PenStyle.NoPen)
        for s in range(6, 0, -1):
            p.setBrush(QColor(0, 0, 0, int(40 - s * 5)))
            p.drawRoundedRect(wx - s, wy - s + (s // 2), ww + 2 * s, wh + 2 * s, 12 + s, 12 + s)
        p.setPen(QColor(self.theme["window_border"]))
        p.setBrush(QColor(self.theme["background"]))
        p.drawRoundedRect(wx, wy, ww, wh, 12, 12)
        if self.show_window_chrome:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(self.theme["title_bar"]))
            p.drawRoundedRect(wx, wy, ww, chrome_h, 12, 12)
            p.drawRect(wx, wy + chrome_h - 12, ww, 12)
            for i, color in enumerate(["#ff5f56", "#ffbd2e", "#27c93f"]):
                p.setBrush(QColor(color))
                p.setPen(Qt.PenStyle.NoPen)
                p.drawEllipse(QPoint(wx + 20 + i * 24, wy + 19), 7, 7)
            p.setPen(QColor(self.theme["title_text"]))
            p.setFont(QFont(self.font_family, max(8, self.font_size // 3)))
            p.drawText(QRect(wx, wy, ww, chrome_h), Qt.AlignCenter, self.title_text)
            p.setPen(QPen(self._qc_accent, 2))
            p.drawLine(wx, wy + chrome_h, wx + ww, wy + chrome_h)
            code_top = wy + chrome_h
        else:
            code_top = wy
        self._code_rect = QRect(wx + 4, code_top, ww - 8, wh - (code_top - wy))
        if self.keyboard_overlay:
            self.keyboard_overlay.reposition(wy + wh + max(8, h // 60))
        p.end()

    def render_frame(self, visible_text: str, vis_err: List[bool],
                     cursor_visible: bool = True, target: Optional[QImage] = None,
                     active_char: Optional[str] = None,
                     key_flash: float = 0.0) -> QImage:
        img = target if target is not None else QImage(self.width, self.height, QImage.Format_RGB32)
        if target is None:
            img.fill(QColor(self.theme["background"]))
        p = QPainter(img)
        p.setRenderHint(QPainter.TextAntialiasing)
        p.drawImage(0, 0, self._bg)
        cr = self._code_rect
        colors = self._tokenize_to_colors(visible_text)
        fg = self._qc_fg
        qc = self._qcolors
        vis_qc = [qc.get(ck, fg) for ck in colors]
        if visible_text != self._layout_nv:
            self._layout_lines = visible_text.split("\n")
            offsets: List[int] = []
            off = 0
            for ln in self._layout_lines:
                offsets.append(off)
                off += len(ln) + 1
            self._layout_offsets = offsets
            self._layout_cursor_line = visible_text.count("\n")
            self._layout_nv = visible_text
        lines = self._layout_lines
        line_offsets = self._layout_offsets
        cursor_line = self._layout_cursor_line
        total_lines = len(self._layout_lines)
        cr_h, cr_top = cr.height(), cr.top()
        max_vis = max(1, -(-cr.height() // self.line_h))
        lh_base = self.line_h
        scroll = 0
        margin_bottom = max(3, max_vis // 4)
        margin_top = 3
        if cursor_line >= scroll + max_vis - margin_bottom:
            scroll = max(0, cursor_line - max_vis + margin_bottom + 1)
        if cursor_line < scroll + margin_top:
            scroll = max(0, cursor_line - margin_top)
        if scroll > max(0, total_lines - max_vis):
            scroll = max(0, total_lines - max_vis)
        ln_width = (len(str(total_lines + scroll)) * self.char_w + 16) if self.show_line_numbers else 0
        current_scroll_line = cursor_line - scroll
        line_y_arr: List[int] = []
        line_h_arr: List[int] = []
        y_acc = cr_top
        for si in range(max_vis):
            li = scroll + si
            if li >= total_lines:
                break
            line_y_arr.append(y_acc)
            line_h_arr.append(lh_base)
            y_acc += lh_base
        n_drawn = len(line_y_arr)
        if 0 <= current_scroll_line < n_drawn:
            p.fillRect(cr.left(), line_y_arr[current_scroll_line],
                       cr.width(), line_h_arr[current_scroll_line], self._qc_current_line)
            p.setPen(QPen(self._qc_accent, 2))
            p.drawLine(cr.left(), line_y_arr[current_scroll_line],
                       cr.left(), line_y_arr[current_scroll_line] + line_h_arr[current_scroll_line])
        if self.show_line_numbers and ln_width > 0:
            sep_x = cr.left() + ln_width
            sc = QColor(self._qc_ln)
            sc.setAlpha(60)
            p.setPen(QPen(sc, 1))
            p.drawLine(sep_x, cr.top(), sep_x, cr.top() + max_vis * lh_base)
        p.setClipRect(cr)
        p.setFont(self.font)
        x0 = cr.left() + ln_width
        n_vis_chars = len(visible_text)
        typed_lines_count = visible_text.count("\n") + 1
        for si in range(n_drawn):
            li = scroll + si
            lh = line_h_arr[si]
            y = line_y_arr[si]
            global_off = line_offsets[li]
            if self.show_line_numbers:
                if li + 1 <= typed_lines_count:
                    color = self._qc_ln_active if li == cursor_line else self._qc_ln
                else:
                    color = QColor(self._qc_ln)
                    color.setAlpha(40)
                p.setPen(color)
                p.drawText(QRect(cr.left(), y, ln_width, lh),
                           Qt.AlignRight | Qt.AlignVCenter, str(li + 1))
            line = lines[li]
            if not line:
                if cursor_visible and li == cursor_line:
                    self._draw_caret(p, int(x0), int(y + lh * 0.15), max(4, lh - 10))
                continue
            char_x = self._get_line_layout(line)
            cur_qc = vis_qc[global_off] if global_off < n_vis_chars else fg
            cur_err = vis_err[global_off] if global_off < len(vis_err) else False
            run_start = 0
            for j in range(1, len(line) + 1):
                next_qc = fg
                next_err = False
                if j < len(line):
                    gp = global_off + j
                    next_qc = vis_qc[gp] if gp < n_vis_chars else fg
                    next_err = vis_err[gp] if gp < len(vis_err) else False
                if j == len(line) or next_qc is not cur_qc or next_err is not cur_err:
                    run_text = line[run_start:j].replace("\t", " " * self.tab_size)
                    p.setPen(cur_qc)
                    p.drawText(QPoint(int(x0 + char_x[run_start]), int(y + lh * 0.78)), run_text)
                    if cur_err:
                        p.setPen(QPen(QColor("#ff5555"), 1.5))
                        uw_y = int(y + lh * 0.85)
                        ux_start = int(x0 + char_x[run_start])
                        run_w = self.fm.horizontalAdvance(run_text)
                        ux_end = ux_start + run_w
                        uw_step = 4
                        path = QPainterPath()
                        path.moveTo(ux_start, uw_y)
                        uw_x = ux_start
                        up = True
                        while uw_x < ux_end:
                            next_x = min(uw_x + uw_step, ux_end)
                            path.lineTo(next_x, uw_y - (3 if up else 0))
                            uw_x = next_x
                            up = not up
                        p.drawPath(path)
                    cur_qc = next_qc
                    cur_err = next_err
                    run_start = j
            if cursor_visible and li == cursor_line:
                n_ch = len(line)
                if n_ch < len(char_x):
                    self._draw_caret(p, int(x0 + char_x[n_ch]), int(y + lh * 0.15), max(4, lh - 10))
                else:
                    last_x = char_x[-1] if char_x else 0
                    last_char = line[-1] if line else " "
                    last_w = self._tab_advance if last_char == "\t" else self.fm.horizontalAdvance(last_char)
                    self._draw_caret(p, int(x0 + last_x + last_w), int(y + lh * 0.15),
                                     max(4, lh - 10), " ")
        p.setClipping(False)
        if self.keyboard_overlay:
            ak = None
            kf = 0.0
            if active_char is not None and key_flash > 0:
                ak = self.keyboard_overlay.resolve_key(active_char)
                kf = key_flash
            self.keyboard_overlay.draw(p, active_key=ak, flash=kf)
        if self.show_watermark:
            wm_font = QFont(self.font_family, max(8, self.font_size // 3))
            p.setFont(wm_font)
            p.setPen(QColor(self._qc_ln))
            wm = f"{datetime.now().strftime('%Y-%m-%d %H:%M')}  |  {self.title_text}"
            fm = QFontMetrics(wm_font)
            p.drawText(self.width - fm.horizontalAdvance(wm) - 20, self.height - 10, wm)
        p.end()
        return img

    def _draw_caret(self, p: QPainter, x: int, y: int, h: int, char: str = " ") -> None:
        cw = max(2, self.fm.horizontalAdvance(char))
        ch = max(4, h - 2)
        if self.cursor_glow:
            gc = QColor(self._qc_cursor)
            gc.setAlpha(80)
            p.fillRect(x - 2, y - 1, cw + 4, ch + 2, gc)
            gc.setAlpha(140)
            p.fillRect(x - 1, y, cw + 2, ch, gc)
        p.fillRect(x, y, cw, ch, self._qc_cursor)
        if char not in (" ", "\t"):
            p.setPen(QColor(self.theme["background"]))
            p.drawText(QRect(int(x), int(y), int(cw), int(ch)), Qt.AlignCenter, char)


# ═══════════════════════════════════════════════════════════════════
# SECTION 11 — MULTI-PANE COMPOSITION
# ═══════════════════════════════════════════════════════════════════

class MultiPaneRenderer:
    __slots__ = ("panes", "frame_w", "frame_h", "num_panes",
                 "pane_layout", "gap", "bg_color", "pane_rects")

    def __init__(self, panes: List[Tuple[CodeRenderer, TypingAnimator]],
                 frame_w: int, frame_h: int, num_panes: int = 2,
                 pane_layout: str = "Side by Side (50/50)",
                 gap: int = 20, bg_color: str = "#0d0d12"):
        self.panes = panes
        self.frame_w = frame_w
        self.frame_h = frame_h
        self.num_panes = max(1, min(num_panes, len(panes)))
        self.pane_layout = pane_layout
        self.gap = gap
        self.bg_color = bg_color
        self.pane_rects = self._compute_pane_rects()

    def _compute_pane_rects(self) -> List[QRect]:
        W, H, g, n = self.frame_w, self.frame_h, self.gap, self.num_panes
        if n == 1:
            return [QRect(0, 0, W, H)]
        if n == 2:
            l = self.pane_layout
            match l:
                case "Stacked (50/50)":
                    ph = (H - g) // 2
                    y_start = (H - (2 * ph + g)) // 2
                    return [QRect(0, y_start, W, ph), QRect(0, y_start + ph + g, W, ph)]
                case "Junior Big (70/30)":
                    pw_l = int((W - g) * 0.7)
                    return [QRect(0, 0, pw_l, H), QRect(pw_l + g, 0, W - g - pw_l, H)]
                case "Senior Big (70/30)":
                    pw_l = int((W - g) * 0.3)
                    return [QRect(0, 0, pw_l, H), QRect(pw_l + g, 0, W - g - pw_l, H)]
                case "PIP - Senior Big (Junior Small)":
                    pip_w, pip_h = int(W * 0.4), int(H * 0.4)
                    return [QRect(W - pip_w - g, H - pip_h - g, pip_w, pip_h), QRect(0, 0, W, H)]
                case "PIP - Junior Big (Senior Small)":
                    pip_w, pip_h = int(W * 0.4), int(H * 0.4)
                    return [QRect(0, 0, W, H), QRect(W - pip_w - g, H - pip_h - g, pip_w, pip_h)]
                case _:
                    pw = (W - g) // 2
                    return [QRect(0, 0, pw, H), QRect(pw + g, 0, pw, H)]
        pw, ph = (W - g) // 2, (H - g) // 2
        return [QRect(0, 0, pw, ph), QRect(pw + g, 0, pw, ph),
                QRect(0, ph + g, pw, ph), QRect(pw + g, ph + g, pw, ph)]

    def duration(self) -> float:
        return max(anim.duration() for _, anim in self.panes) if self.panes else 0.0

    def char_timestamps_all(self) -> List[Tuple[float, str]]:
        all_ts: List[Tuple[float, str]] = []
        for _, anim in self.panes:
            all_ts.extend(anim.char_timestamps())
        return all_ts

    def compute_state(self, t: float) -> Tuple:
        states = []
        for renderer, animator in self.panes:
            nv = animator.visible_at(t)
            cur_vis = True
            if nv > 0:
                idx = bisect.bisect_right(animator._timestamps, t)
                if idx > 0:
                    last_ts = animator.timeline[idx - 1][0]
                    if t - last_ts > 0.25:
                        cur_vis = (int((t - last_ts) / renderer.CURSOR_BLINK) % 2) == 0
            active_char, key_flash = animator.active_key_at(t)
            if not renderer.keyboard_overlay:
                active_char = None
                key_flash = 0.0
            vis_text = animator.text_snapshots[nv]
            vis_err = animator.error_snapshots[nv]
            states.append((vis_text, vis_err, cur_vis, active_char, round(key_flash, 2)))
        return tuple(states)

    def render_frame(self, t: float, target: Optional[QImage] = None,
                    precomputed_state: Optional[Tuple] = None) -> QImage:
        img = target if target is not None else QImage(self.frame_w, self.frame_h, QImage.Format_RGB32)
        img.fill(QColor(self.bg_color))
        p = QPainter(img)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        if precomputed_state is None:
            precomputed_state = self.compute_state(t)
        sorted_indices = sorted(range(len(self.panes)),
                               key=lambda i: self.pane_rects[i].width() * self.pane_rects[i].height(),
                               reverse=True)
        for i in sorted_indices:
            if i >= len(precomputed_state):
                break
            vis_text, vis_err, cur_vis, active_char, key_flash = precomputed_state[i]
            renderer, animator = self.panes[i]
            rect = self.pane_rects[i]
            pane_img = renderer.render_frame(vis_text, vis_err, cur_vis,
                                             active_char=active_char, key_flash=key_flash)
            p.drawImage(rect.topLeft(), pane_img)
        if self.num_panes == 2:
            p.setPen(QPen(QColor(self.bg_color), max(4, self.gap // 2)))
            match self.pane_layout:
                case "Side by Side (50/50)":
                    p.drawLine(self.pane_rects[0].right() + self.gap // 2, 0,
                               self.pane_rects[0].right() + self.gap // 2, self.frame_h)
                case "Stacked (50/50)":
                    p.drawLine(0, self.pane_rects[0].bottom() + self.gap // 2,
                               self.frame_w, self.pane_rects[0].bottom() + self.gap // 2)
                case "Junior Big (70/30)" | "Senior Big (70/30)":
                    p.drawLine(self.pane_rects[0].right() + self.gap // 2, 0,
                               self.pane_rects[0].right() + self.gap // 2, self.frame_h)
                case _:
                    if "PIP" in self.pane_layout:
                        pip_rect = (self.pane_rects[0]
                                    if (self.pane_rects[0].width() * self.pane_rects[0].height()
                                        < self.pane_rects[1].width() * self.pane_rects[1].height())
                                    else self.pane_rects[1])
                        p.setPen(QPen(QColor(self.bg_color), max(4, self.gap // 2)))
                        p.drawRect(pip_rect.adjusted(-self.gap // 2, -self.gap // 2,
                                                     self.gap // 2, self.gap // 2))
        p.end()
        return img


# ═══════════════════════════════════════════════════════════════════
# SECTION 12 — EXPORT CONFIGURATION & ENCODER STRATEGY
# ═══════════════════════════════════════════════════════════════════

EXPORT_FORMATS: Dict[str, dict] = {
    "YouTube (16:9)": {
        "resolutions": OrderedDict([
            ("1920x1080", (1920, 1080)),
            ("1280x720", (1280, 720)),
            ("3840x2160", (3840, 2160)),
        ]),
        "orientation": "landscape",
    },
    "YouTube Shorts (9:16)": {
        "resolutions": OrderedDict([
            ("1080x1920", (1080, 1920)),
            ("720x1280", (720, 1280)),
        ]),
        "orientation": "portrait",
    },
}

ENCODERS: Dict[str, dict] = {
    "YouTube Pro (H.264/AAC)": {
        "base": ["-c:v", "libx264", "-preset", "slow", "-crf", "17",
                 "-profile:v", "high", "-pix_fmt", "yuv420p"],
        "use_dynamic_vbv": True, "use_dynamic_gop": True, "color_tags": True,
    },
    "x264 (CPU, Best Quality)": {
        "base": ["-c:v", "libx264", "-preset", "slow", "-crf", "16", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True, "color_tags": True,
    },
    "x264 (CPU, Fast)": {
        "base": ["-c:v", "libx264", "-preset", "medium", "-crf", "20", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True, "color_tags": True,
    },
    "NVENC (NVIDIA)": {
        "base": ["-c:v", "h264_nvenc", "-preset", "p5", "-rc", "vbr",
                 "-cq", "19", "-b:v", "0", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True, "color_tags": True,
    },
    "QSV (Intel)": {
        "base": ["-c:v", "h264_qsv", "-preset", "medium", "-global_quality", "19", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True, "color_tags": True,
    },
    "AMF (AMD)": {
        "base": ["-c:v", "h264_amf", "-preset", "speed", "-rc", "cqp",
                 "-qp_i", "19", "-qp_p", "19", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True, "color_tags": True,
    },
}

QUALITY_PRESETS: Dict[str, dict] = {
    "Draft (720p, 30fps)":   {"res": "1280x720",  "fps": 30, "encoder": "x264 (CPU, Fast)"},
    "Medium (1080p, 30fps)": {"res": "1920x1080", "fps": 30, "encoder": "YouTube Pro (H.264/AAC)"},
    "High (1080p, 60fps)":   {"res": "1920x1080", "fps": 60, "encoder": "YouTube Pro (H.264/AAC)"},
    "Ultra (4K, 60fps)":     {"res": "3840x2160", "fps": 60, "encoder": "YouTube Pro (H.264/AAC)"},
}

@dataclass(slots=True)
class ExportConfig:
    junior_code: str
    senior_code: str
    name: str
    fmt: str
    res: str
    theme: str
    j_font: str
    s_font: str
    font_size_auto: bool
    font_size: int
    chrome: bool
    ln: bool
    cursor_glow: bool
    watermark: bool
    bg_image_path: str
    show_kb: bool
    kb_layout: str
    kb_pos: str
    kb_op: float
    j_wpm: int
    j_pause: float
    j_burst: float
    s_wpm: int
    s_pause: float
    s_burst: float
    start_pause: float
    end_pause: float
    lang: str
    pane_layout: str
    pad: int
    gap: int


class ExportConfigBuilder:
    def __init__(self):
        self._fields: Dict[str, Any] = {}

    def junior_code(self, code: str) -> "ExportConfigBuilder":
        self._fields["junior_code"] = code; return self
    def senior_code(self, code: str) -> "ExportConfigBuilder":
        self._fields["senior_code"] = code; return self
    def name(self, n: str) -> "ExportConfigBuilder":
        self._fields["name"] = n; return self
    def fmt(self, f: str) -> "ExportConfigBuilder":
        self._fields["fmt"] = f; return self
    def res(self, r: str) -> "ExportConfigBuilder":
        self._fields["res"] = r; return self
    def theme(self, t: str) -> "ExportConfigBuilder":
        self._fields["theme"] = t; return self
    def j_font(self, f: str) -> "ExportConfigBuilder":
        self._fields["j_font"] = f; return self
    def s_font(self, f: str) -> "ExportConfigBuilder":
        self._fields["s_font"] = f; return self
    def font_size_auto(self, v: bool) -> "ExportConfigBuilder":
        self._fields["font_size_auto"] = v; return self
    def font_size(self, s: int) -> "ExportConfigBuilder":
        self._fields["font_size"] = s; return self
    def chrome(self, c: bool) -> "ExportConfigBuilder":
        self._fields["chrome"] = c; return self
    def ln(self, l: bool) -> "ExportConfigBuilder":
        self._fields["ln"] = l; return self
    def cursor_glow(self, g: bool) -> "ExportConfigBuilder":
        self._fields["cursor_glow"] = g; return self
    def watermark(self, w: bool) -> "ExportConfigBuilder":
        self._fields["watermark"] = w; return self
    def bg_image_path(self, p: str) -> "ExportConfigBuilder":
        self._fields["bg_image_path"] = p; return self
    def show_kb(self, s: bool) -> "ExportConfigBuilder":
        self._fields["show_kb"] = s; return self
    def kb_layout(self, l: str) -> "ExportConfigBuilder":
        self._fields["kb_layout"] = l; return self
    def kb_pos(self, p: str) -> "ExportConfigBuilder":
        self._fields["kb_pos"] = p; return self
    def kb_op(self, o: float) -> "ExportConfigBuilder":
        self._fields["kb_op"] = o; return self
    def j_wpm(self, w: int) -> "ExportConfigBuilder":
        self._fields["j_wpm"] = w; return self
    def j_pause(self, p: float) -> "ExportConfigBuilder":
        self._fields["j_pause"] = p; return self
    def j_burst(self, b: float) -> "ExportConfigBuilder":
        self._fields["j_burst"] = b; return self
    def s_wpm(self, w: int) -> "ExportConfigBuilder":
        self._fields["s_wpm"] = w; return self
    def s_pause(self, p: float) -> "ExportConfigBuilder":
        self._fields["s_pause"] = p; return self
    def s_burst(self, b: float) -> "ExportConfigBuilder":
        self._fields["s_burst"] = b; return self
    def start_pause(self, s: float) -> "ExportConfigBuilder":
        self._fields["start_pause"] = s; return self
    def end_pause(self, e: float) -> "ExportConfigBuilder":
        self._fields["end_pause"] = e; return self
    def lang(self, l: str) -> "ExportConfigBuilder":
        self._fields["lang"] = l; return self
    def pane_layout(self, p: str) -> "ExportConfigBuilder":
        self._fields["pane_layout"] = p; return self
    def pad(self, p: int) -> "ExportConfigBuilder":
        self._fields["pad"] = p; return self
    def gap(self, g: int) -> "ExportConfigBuilder":
        self._fields["gap"] = g; return self

    def build(self) -> ExportConfig:
        return ExportConfig(**self._fields)


def _build_panes_from_config(cfg: ExportConfig) -> MultiPaneRenderer:
    fmt_data = EXPORT_FORMATS.get(cfg.fmt, EXPORT_FORMATS["YouTube (16:9)"])
    w, h = fmt_data["resolutions"].get(cfg.res, (1920, 1080))
    theme = THEMES[cfg.theme]
    jp = TypingProfile(name="Junior Dev", wpm=cfg.j_wpm, pause_freq=cfg.j_pause,
                       burst_chance=cfg.j_burst, start_pause=cfg.start_pause,
                       end_pause=cfg.end_pause, error_chance=0.04)
    sp = TypingProfile(name="Senior Dev", wpm=cfg.s_wpm, pause_freq=cfg.s_pause,
                       burst_chance=cfg.s_burst, start_pause=cfg.start_pause,
                       end_pause=cfg.end_pause, error_chance=0.01)
    panes: List[Tuple[CodeRenderer, TypingAnimator]] = []
    for i, (code, profile, title, accent_key) in enumerate([
        (cfg.junior_code, jp, f"👶 Junior Dev — {cfg.name}", "junior_accent"),
        (cfg.senior_code, sp, f"🧓 Senior Dev — {cfg.name}", "senior_accent"),
    ]):
        match cfg.pane_layout:
            case "Side by Side (50/50)": pw, ph = (w - cfg.gap) // 2, h
            case "Stacked (50/50)": pw, ph = w, (h - cfg.gap) // 2
            case "Junior Big (70/30)":
                pw = int((w - cfg.gap) * 0.7) if i == 0 else (w - cfg.gap) - int((w - cfg.gap) * 0.7)
                ph = h
            case "Senior Big (70/30)":
                pw = int((w - cfg.gap) * 0.3) if i == 0 else (w - cfg.gap) - int((w - cfg.gap) * 0.3)
                ph = h
            case "PIP - Senior Big (Junior Small)":
                pw = int(w * 0.4) if i == 0 else w
                ph = int(h * 0.4) if i == 0 else h
            case "PIP - Junior Big (Senior Small)":
                pw = w if i == 0 else int(w * 0.4)
                ph = h if i == 0 else int(h * 0.4)
            case _: pw, ph = (w - cfg.gap) // 2, h
        language = cfg.lang
        if language == "Auto":
            ext = os.path.splitext(cfg.name)[1].lower()
            ext_map = {".py": "Python", ".js": "JavaScript", ".cpp": "CFamily", ".cs": "CSharp"}
            language = ext_map.get(ext, "Text")
        code_lines = code.count("\n") + 1
        kb_overlay = None
        kb_h = 0
        if cfg.show_kb:
            kb_overlay = KeyboardOverlay(pw, ph, cfg.kb_layout, theme,
                                         (ph - 2 * cfg.pad) // 3, cfg.kb_pos, cfg.kb_op)
            kb_h = kb_overlay.height_needed()
        current_font = cfg.j_font if i == 0 else cfg.s_font
        font_size = (CodeRenderer.auto_font_size(code_lines, pw, ph, cfg.pad, cfg.chrome,
                      cfg.ln, 4, code, current_font, kb_h) if cfg.font_size_auto
                     else max(8, int(cfg.font_size)))
        renderer = CodeRenderer(width=pw, height=ph, theme_name=cfg.theme,
                                font_family=current_font, font_size=font_size,
                                title_text=title, language=language,
                                keyboard_overlay=kb_overlay, padding=cfg.pad,
                                show_window_chrome=cfg.chrome,
                                show_line_numbers=cfg.ln,
                                bg_image_path=cfg.bg_image_path if i == 0 else None,
                                total_code_lines=code_lines,
                                cursor_glow=cfg.cursor_glow,
                                show_watermark=cfg.watermark and i == 0,
                                accent_color=theme.get(accent_key, "#7aa2f7"))
        animator = TypingAnimator(code, profile, seed=i * 1000 + 42)
        panes.append((renderer, animator))
    return MultiPaneRenderer(panes=panes, frame_w=w, frame_h=h, num_panes=2,
                             pane_layout=cfg.pane_layout, gap=cfg.gap)


# ═══════════════════════════════════════════════════════════════════
# SECTION 13 — MEDIA EXPORT
# ═══════════════════════════════════════════════════════════════════

def _format_eta(seconds: float) -> str:
    if seconds < 1:
        return "< 1s"
    if seconds < 60:
        return f"{int(seconds)}s"
    m, s = divmod(int(seconds), 60)
    if m < 60:
        return f"{m}m {s}s"
    h, m = divmod(m, 60)
    return f"{h}h {m}m {s}s"


def _subprocess_startup_info() -> Optional[subprocess.STARTUPINFO]:
    if platform.system() == "Windows":
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        si.wShowWindow = subprocess.SW_HIDE
        return si
    return None


@contextmanager
def temp_directory(prefix: str = "export_"):
    tmp = tempfile.mkdtemp(dir=str(TEMP_DIR), prefix=prefix)
    try:
        yield tmp
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


@contextmanager
def ffmpeg_pipeline(cmd: List[str]):
    si = _subprocess_startup_info()
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                            startupinfo=si)
    try:
        yield proc
    finally:
        with suppress(Exception):
            if proc.stdin:
                proc.stdin.close()
        proc.wait(timeout=30)


class AudioWorker(QObject):
    finished = Signal(object)
    error = Signal(str)

    def __init__(self, sound_params: Tuple[str, bool, float],
                 timestamps: List[Tuple[float, str]],
                 volume: float, filepath: Optional[str] = None,
                 bgm_path: Optional[str] = None,
                 bgm_volume: float = 0.3, bgm_duck: float = 0.6):
        super().__init__()
        self.sound_params = sound_params
        self.timestamps = timestamps
        self.volume = volume
        self.filepath = filepath
        self.bgm_path = bgm_path
        self.bgm_volume = bgm_volume
        self.bgm_duck = bgm_duck

    @Slot()
    def run(self):
        preset, stereo, reverb_amt = self.sound_params
        log.info("AudioWorker started — preset=%s stereo=%s reverb=%.2f events=%d vol=%.2f duck=%.2f",
                 preset, stereo, reverb_amt, len(self.timestamps), self.volume, self.bgm_duck)
        try:
            sg = SimpleSoundGen(sr=44100, preset=preset, stereo=stereo, reverb_amt=reverb_amt)
            if self.filepath and self.bgm_path and os.path.exists(self.bgm_path):
                tmp_typing = self.filepath + ".typing.wav"
                sg.generate_track(self.timestamps, tmp_typing, self.volume)
                try:
                    dur_proc = subprocess.run(
                        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
                         "-of", "default=noprint_wrappers=1:nokey=1", tmp_typing],
                        capture_output=True, text=True, timeout=10,
                        startupinfo=_subprocess_startup_info())
                    audio_dur = float(dur_proc.stdout.strip())
                    fade_out_str = f"afade=t=out:st={max(0, audio_dur-3):.3f}:d=3,"
                except Exception:
                    fade_out_str = ""
                sc_ratio = max(1.0, 1.0 + self.bgm_duck * 9.0)
                sc_threshold = max(0.005, 0.10 - self.bgm_duck * 0.08)
                sc_makeup = 1.0 + self.bgm_duck * 1.0
                cmd = ["ffmpeg", "-y", "-i", tmp_typing, "-i", self.bgm_path,
                       "-filter_complex",
                       f"[1:a]highpass=f=60,lowpass=f=5500,volume={self.bgm_volume},"
                       f"afade=t=in:st=0:d=2,{fade_out_str}[bgm_eq];"
                       f"[bgm_eq][0:a]sidechaincompress="
                       f"threshold={sc_threshold:.3f}:ratio={sc_ratio:.2f}:"
                       f"attack=0.015:release=0.3:makeup={sc_makeup:.2f}[bgm_duck];"
                       f"[0:a][bgm_duck]amix=inputs=2:duration=first:normalize=0,"
                       f"alimiter=limit=0.95[aout]",
                       "-map", "[aout]", "-b:a", "256k", "-ar", "48000", self.filepath]
                si = _subprocess_startup_info()
                proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL,
                                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                                       startupinfo=si)
                _, stderr = proc.communicate(timeout=180)
                if proc.returncode != 0:
                    shutil.move(tmp_typing, self.filepath)
                else:
                    os.remove(tmp_typing)
            elif self.filepath:
                sg.generate_track(self.timestamps, self.filepath, self.volume)
            else:
                pcm = sg.generate_pcm(self.timestamps, self.volume)
                if len(pcm) > 0:
                    self.finished.emit(_pcm_to_wav_bytes(pcm, sg.sr, 2 if stereo else 1))
                else:
                    self.finished.emit(None)
                return
            self.finished.emit(self.filepath if self.filepath else None)
        except Exception as e:
            log.error("AudioWorker FAILED: %s", e, exc_info=True)
            self.error.emit(str(e))


class VideoExporter(QThread):
    progress = Signal(int)
    status = Signal(str)
    finished_ok = Signal(str)
    error = Signal(str)

    CHUNK_DURATION: Final[float] = 300.0

    def __init__(self, export_config: ExportConfig, output: str,
                 fps: int = 30, sound_params: Optional[Tuple[str, bool, float]] = None,
                 volume: float = 0.5, encoder_name: str = "YouTube Pro (H.264/AAC)",
                 bgm_path: Optional[str] = None, bgm_volume: float = 0.3,
                 bgm_duck: float = 0.6, parent=None):
        super().__init__(parent)
        self.setObjectName("VideoExporter")
        self.config = export_config
        self.output = output
        self.fps = fps
        self.sound_params = sound_params
        self.volume = volume
        self.encoder_name = encoder_name
        self.bgm_path = bgm_path
        self.bgm_volume = bgm_volume
        self.bgm_duck = bgm_duck
        self.multi_pane = _build_panes_from_config(self.config)
        self._cancel = threading.Event()

    def cancel(self) -> None:
        self._cancel.set()

    def is_cancelled(self) -> bool:
        return self._cancel.is_set()

    def run(self) -> None:
        audio_executor: Optional[ThreadPoolExecutor] = None
        try:
            total_dur = self.multi_pane.duration()
            num_chunks = max(1, math.ceil(total_dur / self.CHUNK_DURATION))

            with temp_directory() as tmp_dir:
                audio_executor = ThreadPoolExecutor(max_workers=1) if self.sound_params else None
                audio_future: Optional[Future] = None
                final_audio = os.path.join(tmp_dir, "final_audio.wav")

                if audio_executor:
                    self.status.emit("Starting audio generation...")
                    all_ts = self.multi_pane.char_timestamps_all()
                    if all_ts:
                        audio_future = audio_executor.submit(self._gen_full_audio, all_ts, final_audio)

                video_chunks: List[str] = []
                for c_idx in range(num_chunks):
                    if self._cancel.is_set():
                        break
                    start_t = c_idx * self.CHUNK_DURATION
                    end_t = min(total_dur, start_t + self.CHUNK_DURATION)
                    start_frame = int(start_t * self.fps)
                    n_chunk = math.ceil(end_t * self.fps) - start_frame
                    self.status.emit(f"Rendering Video Chunk {c_idx + 1}/{num_chunks}...")
                    chunk_vid = os.path.join(tmp_dir, f"vid_{c_idx}.mp4")
                    if not self._render_chunk_video(start_frame, n_chunk, chunk_vid):
                        raise RenderingError(f"Failed to render video for chunk {c_idx + 1}")
                    video_chunks.append(chunk_vid)
                    self.progress.emit(int(((c_idx + 1) / num_chunks) * 80))

                if self._cancel.is_set():
                    self.error.emit("Cancelled")
                    return

                self.status.emit("Stitching video chunks...")
                final_video = os.path.join(tmp_dir, "final_video.mp4")
                self._concat_files(video_chunks, final_video)

                if audio_future:
                    self.status.emit("Waiting for audio generation to finish...")
                    audio_ok = audio_future.result()
                    if audio_ok:
                        self.status.emit("Muxing final video and audio...")
                        self._mux_final(final_video, final_audio, self.output)
                    else:
                        shutil.move(final_video, self.output)
                else:
                    shutil.move(final_video, self.output)

                self.progress.emit(100)
                self.status.emit(f"Done → {self.output}")
                self.finished_ok.emit(self.output)

        except Exception as e:
            log.error("=== VideoExporter FAILED ===", exc_info=True)
            self.error.emit(str(e))
        finally:
            if audio_executor:
                audio_executor.shutdown(wait=True)

    def _gen_full_audio(self, ts: List[Tuple[float, str]], filepath: str) -> bool:
        try:
            preset, stereo, reverb_amt = self.sound_params
            sg = SimpleSoundGen(sr=44100, preset=preset, stereo=stereo, reverb_amt=reverb_amt)
            sg.generate_track(ts, filepath, self.volume)
            return os.path.exists(filepath) and os.path.getsize(filepath) > 44
        except Exception as e:
            log.error("Audio gen FAILED: %s", e, exc_info=True)
            return False

    def _concat_files(self, paths: List[str], out_path: str) -> None:
        concat_path = os.path.join(os.path.dirname(out_path), "concat_list.txt")
        with open(concat_path, "w", encoding="utf-8") as f:
            for p in paths:
                safe = p.replace("\\", "/").replace("'", "\\'")
                f.write(f"file '{safe}'\n")
        cmd = ["ffmpeg", "-y", "-f", "concat", "-safe", "0",
               "-i", concat_path, "-c", "copy", out_path]
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL,
                                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                                startupinfo=_subprocess_startup_info())
        _, stderr = proc.communicate(timeout=max(120, len(paths) * 60))
        if proc.returncode != 0:
            raise FFmpegError(f"Concat failed: {stderr.decode(errors='ignore')[-400:]}")

    def _mux_final(self, vid_path: str, aud_path: str, out_path: str) -> None:
        if self.bgm_path and os.path.exists(self.bgm_path):
            try:
                dur_proc = subprocess.run(
                    ["ffprobe", "-v", "error", "-show_entries", "format=duration",
                     "-of", "default=noprint_wrappers=1:nokey=1", aud_path],
                    capture_output=True, text=True, timeout=15,
                    startupinfo=_subprocess_startup_info())
                audio_dur = float(dur_proc.stdout.strip())
                fade_out_st = max(0.0, audio_dur - 3.0)
                fade_out_str = f"afade=t=out:st={fade_out_st:.3f}:d=3,"
            except Exception:
                fade_out_str = ""

            sc_ratio = max(1.0, 1.0 + self.bgm_duck * 9.0)
            sc_threshold = max(0.005, 0.10 - self.bgm_duck * 0.08)
            sc_makeup = 1.0 + self.bgm_duck * 1.0

            cmd = ["ffmpeg", "-y", "-i", vid_path, "-i", aud_path, "-i", self.bgm_path,
                   "-c:v", "copy",
                   "-filter_complex",
                   f"[2:a]highpass=f=60,lowpass=f=5500,volume={self.bgm_volume},"
                   f"afade=t=in:st=0:d=2,{fade_out_str}"
                   f"aresample=48000[bgm_eq];"
                   f"[bgm_eq][1:a]sidechaincompress="
                   f"threshold={sc_threshold:.3f}:ratio={sc_ratio:.2f}:"
                   f"attack=0.015:release=0.3:makeup={sc_makeup:.2f}[bgm_duck];"
                   f"[1:a][bgm_duck]amix=inputs=2:duration=longest:normalize=0,"
                   f"alimiter=limit=0.95[aout]",
                   "-map", "0:v", "-map", "[aout]",
                   "-c:a", "aac", "-b:a", "256k", "-ar", "48000",
                   "-movflags", "+faststart", out_path]
        else:
            cmd = ["ffmpeg", "-y", "-i", vid_path, "-i", aud_path,
                   "-map", "0:v", "-map", "1:a",
                   "-c:v", "copy", "-c:a", "aac", "-b:a", "256k",
                   "-ar", "48000", "-movflags", "+faststart", out_path]
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL,
                                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                                startupinfo=_subprocess_startup_info())
        _, stderr = proc.communicate(
            timeout=max(120, os.path.getsize(vid_path) // (1024 * 1024) * 2))
        if proc.returncode != 0:
            raise FFmpegError(f"Final mux failed: {stderr.decode(errors='ignore')[-400:]}")

    def _render_chunk_video(self, start_frame: int, n_frames: int,
                           out_path: str, allow_fallback: bool = True) -> bool:
        w, h, fps = self.multi_pane.frame_w, self.multi_pane.frame_h, self.fps
        cmd = ["ffmpeg", "-y", "-f", "rawvideo", "-pix_fmt", "bgra",
               "-s", f"{w}x{h}", "-r", str(fps), "-i", "pipe:0"]
        enc_cfg = ENCODERS.get(self.encoder_name, ENCODERS["YouTube Pro (H.264/AAC)"])
        cmd += enc_cfg["base"]
        if enc_cfg.get("use_dynamic_gop", False):
            gop = int(fps * 2)
            cmd += ["-g", str(gop), "-keyint_min", str(gop), "-sc_threshold", "0"]
        if enc_cfg.get("use_dynamic_vbv", False):
            pixels = w * h
            maxrate = int((pixels / 2073600.0) * 12000000)
            cmd += ["-maxrate", f"{maxrate}", "-bufsize", f"{maxrate * 2}"]
        if enc_cfg.get("color_tags", False):
            cmd += ["-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709"]
        cmd += ["-an", out_path]

        try:
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                                    startupinfo=_subprocess_startup_info())
        except FileNotFoundError:
            self.error.emit("FFmpeg not found on PATH.")
            return False

        stderr_chunks: List[bytes] = []
        def _drain():
            while True:
                chunk = proc.stderr.read(8192)
                if not chunk:
                    break
                stderr_chunks.append(chunk)
        dt = threading.Thread(target=_drain, daemon=True)
        dt.start()

        wq: deque = deque()
        wl = threading.Lock()
        wcv = threading.Condition(wl)
        we: List[str] = []
        wd = [False]

        def _writer():
            try:
                while True:
                    with wl:
                        while not wq and not wd[0]:
                            wcv.wait(timeout=0.5)
                        if not wq and wd[0]:
                            break
                        fd = wq.popleft()
                        if fd is None:
                            break
                    try:
                        proc.stdin.write(fd)
                        proc.stdin.flush()
                    except BrokenPipeError:
                        we.append("BrokenPipe")
                        break
                    except Exception as ex:
                        we.append(str(ex))
                        break
            except Exception as ex:
                we.append(str(ex))
            finally:
                with suppress(Exception):
                    if proc.stdin:
                        proc.stdin.flush()
                        proc.stdin.close()
                wd[0] = True
                with wl:
                    wcv.notify_all()

        wt = threading.Thread(target=_writer, daemon=True)
        wt.start()

        scratch = QImage(w, h, QImage.Format_RGB32)
        for fi in range(n_frames):
            if self._cancel.is_set() or we:
                break
            t = (start_frame + fi) / self.fps
            if fi % 100 == 0:
                self.status.emit(f"Rendering frame {fi}/{n_frames} ({_format_eta(t)})...")
            state = self.multi_pane.compute_state(t)
            qimg = self.multi_pane.render_frame(t, scratch, precomputed_state=state)
            ptr = qimg.constBits()
            try:
                img_bytes = bytes(ptr)
            except TypeError:
                img_bytes = ptr.tobytes()
            except AttributeError:
                ptr.setsize(qimg.sizeInBytes())
                img_bytes = bytes(ptr)
            with wl:
                while len(wq) >= 6:
                    wcv.wait(timeout=0.1)
                if self._cancel.is_set() or we:
                    break
                wq.append(img_bytes)
                wcv.notify_all()

        if not self._cancel.is_set() and not we:
            with wl:
                wq.append(None)
                wcv.notify_all()

        wt.join(timeout=600)

        if we:
            if allow_fallback and self.encoder_name != "x264 (CPU, Fast)":
                self.encoder_name = "x264 (CPU, Fast)"
                self.status.emit("Hardware encoder failed. Retrying with CPU fallback...")
                return self._render_chunk_video(start_frame, n_frames, out_path, allow_fallback=False)
            return False

        proc.wait(timeout=600)
        dt.join(timeout=5)

        if proc.returncode != 0:
            if allow_fallback and self.encoder_name != "x264 (CPU, Fast)":
                self.encoder_name = "x264 (CPU, Fast)"
                self.status.emit("Hardware encoder failed. Retrying with CPU fallback...")
                return self._render_chunk_video(start_frame, n_frames, out_path, allow_fallback=False)
            return False
        return True


# ═══════════════════════════════════════════════════════════════════
# SECTION 14 — UI COMPONENTS (HEAVILY MODIFIED FOR BATCH)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FileItem:
    path: str
    checked: bool = False
    status: str = "Pending"
    output_path: Optional[str] = None
    error: Optional[str] = None
    junior_code: Optional[str] = None
    senior_code: Optional[str] = None


class PythonHighlighter(QSyntaxHighlighter):
    def __init__(self, document):
        super().__init__(document)
        self.rules: List[Tuple[QRegularExpression, QTextCharFormat]] = []
        keyword_fmt = QTextCharFormat()
        keyword_fmt.setForeground(QColor("#ff79c6"))
        keyword_fmt.setFontWeight(QFont.Bold)
        for word in ["def", "class", "return", "if", "else", "elif", "import",
                      "from", "as", "for", "while", "try", "except", "finally",
                      "with", "lambda", "yield", "pass", "break", "continue",
                      "global", "nonlocal", "assert", "del", "in", "is", "not",
                      "and", "or", "True", "False", "None"]:
            self.rules.append((QRegularExpression(rf"\b{word}\b"), keyword_fmt))
        string_fmt = QTextCharFormat()
        string_fmt.setForeground(QColor("#f1fa8c"))
        self.rules.append((QRegularExpression(r'".*?"', QRegularExpression.DotMatchesEverythingOption), string_fmt))
        self.rules.append((QRegularExpression(r"'.*?'", QRegularExpression.DotMatchesEverythingOption), string_fmt))
        self.rules.append((QRegularExpression(r'""".*?"""', QRegularExpression.DotMatchesEverythingOption), string_fmt))
        comment_fmt = QTextCharFormat()
        comment_fmt.setForeground(QColor("#6272a4"))
        comment_fmt.setFontItalic(True)
        self.rules.append((QRegularExpression(r"#[^\n]*"), comment_fmt))
        number_fmt = QTextCharFormat()
        number_fmt.setForeground(QColor("#bd93f9"))
        self.rules.append((QRegularExpression(r"\b\d+\.?\d*\b"), number_fmt))
        func_fmt = QTextCharFormat()
        func_fmt.setForeground(QColor("#50fa7b"))
        self.rules.append((QRegularExpression(r"\b[A-Za-z0-9_]+(?=\()"), func_fmt))

    def highlightBlock(self, text: str) -> None:
        for pattern, fmt in self.rules:
            it = pattern.globalMatch(text)
            while it.hasNext():
                match = it.next()
                self.setFormat(match.capturedStart(), match.capturedLength(), fmt)


_SAMPLE_CODE = '''# No file selected.
# Click a file in the table on the left to load it.
# Or paste your own code here and click "Load Custom Code".
'''


class _BatchTableWidget(QTableWidget):
    def mousePressEvent(self, event):
        super().mousePressEvent(event)
        if event.button() != Qt.LeftButton:
            return
        pos = event.position().toPoint() if hasattr(event, 'position') else event.pos()
        item = self.itemAt(pos)
        if not item:
            return
        if item.column() != 0:
            ci = self.item(item.row(), 0)
            if ci is not None:
                ns = Qt.CheckState.Checked if ci.checkState() == Qt.CheckState.Unchecked else Qt.CheckState.Unchecked
                ci.setCheckState(ns)


class MainWindow(QMainWindow):
    KB_POS_MAP: Final[Dict[str, str]] = {
        "Bottom Center": "bottom_center", "Bottom Right": "bottom_right",
        "Bottom Left": "bottom_left", "Center Left": "center_left",
        "Center Right": "center_right", "Top Center": "top_center",
        "Top Right": "top_right", "Top Left": "top_left",
    }

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Junior vs Senior Dev — Code Typing Studio (Batch Edition)")
        self.setMinimumSize(1200, 800)
        self.resize(1400, 900)
        self.setAcceptDrops(True)
        self._input_dir = str(INPUT_DIR)
        self._exporter: Optional[VideoExporter] = None
        self._loading_settings = False
        self._bg_image_path = ""
        self._preview_progress = 0.0
        self._preview_animating = False
        self._preview_anim_t = 0.0
        self._preview_loop = False
        self._preview_timer = QTimer(self)
        self._preview_timer.setTimerType(Qt.PreciseTimer)
        self._preview_timer.setInterval(16)
        self._preview_timer.timeout.connect(self._advance_preview)
        self._preview_clock = QElapsedTimer()
        self._cached_key: Optional[tuple] = None
        self._cached_mp: Optional[MultiPaneRenderer] = None
        self._cached_panes: List = []
        self._preview_scratch: Optional[QImage] = None
        self._current_junior_code = ""
        self._current_senior_code = ""
        self._current_name = "Empty"
        self._audio_workers: List[QThread] = []
        self._shortcuts: List[QShortcut] = []

        self._items: List[FileItem] = []
        self._item_paths: set = set()
        self._export_queue: List[FileItem] = []
        self._checkbox_anchor: Optional[int] = None
        self._batch_total = 0
        self._batch_done = 0

        self._audio_player = QMediaPlayer(self)
        self._audio_out = QAudioOutput(self)
        self._audio_player.setAudioOutput(self._audio_out)
        self._audio_buf = None
        self._audio_tmp_file: Optional[str] = None
        self._bgm_player = QMediaPlayer(self)
        self._bgm_out = QAudioOutput(self)
        self._bgm_player.setAudioOutput(self._bgm_out)
        self._build_ui()
        self._connect_signals()
        self._load_settings()
        self._scan_input_dir()
        QTimer.singleShot(300, self._update_preview)

    def dragEnterEvent(self, event: QDragEnterEvent) -> None:
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event: QDropEvent) -> None:
        for url in event.mimeData().urls():
            path = url.toLocalFile()
            if os.path.isfile(path) and os.path.splitext(path)[1].lower() in SUPPORTED_EXTENSIONS:
                if path not in self._item_paths:
                    self._items.append(FileItem(path=path, checked=True))
                    self._item_paths.add(path)
        self._refresh_table()
        self._invalidate_and_schedule()

    def _play_audio_bytes(self, data: bytes, vol: float) -> None:
        if not self._audio_player or not data:
            return
        self._audio_player.stop()
        if self._audio_tmp_file:
            old = self._audio_tmp_file
            self._audio_tmp_file = None
            QTimer.singleShot(2000, lambda f=old: self._safe_delete_file(f))
        fd, tmp_path = tempfile.mkstemp(suffix='.wav', dir=str(TEMP_DIR))
        try:
            with os.fdopen(fd, 'wb') as f:
                f.write(data)
            self._audio_tmp_file = tmp_path
            self._audio_out.setVolume(max(0.0, min(1.0, vol)))
            self._audio_player.setSource(QUrl.fromLocalFile(tmp_path))
            self._audio_player.play()
        except Exception:
            self._safe_delete_file(tmp_path)

    @staticmethod
    def _safe_delete_file(path: Optional[str]) -> None:
        try:
            if path and os.path.exists(path):
                os.unlink(path)
        except Exception:
            pass

    def _build_ui(self) -> None:
        central = QWidget()
        self.setCentralWidget(central)
        root = QHBoxLayout(central)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)
        self._build_explorer(root)
        right = QWidget()
        rl = QVBoxLayout(right)
        rl.setContentsMargins(0, 0, 0, 0)
        rl.setSpacing(0)
        self._build_header(rl)
        self.tabs = QTabWidget()
        self._build_preview_tab()
        self._build_settings_tab()
        rl.addWidget(self.tabs, 1)
        self._build_controls(rl)
        root.addWidget(right, 1)
        self.statusBar().showMessage("Ready — Scan files, check them, then Export")

    def _build_explorer(self, parent_layout: QHBoxLayout) -> None:
        panel = QWidget()
        panel.setFixedWidth(320)
        pl = QVBoxLayout(panel)
        pl.setContentsMargins(0, 0, 0, 0)
        pl.setSpacing(0)

        header = QFrame()
        header.setFixedHeight(40)
        header.setStyleSheet("QFrame { background-color: #1e1e2e; border-bottom: 1px solid #11111b; }")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(12, 0, 8, 0)
        title = QLabel("📂 FILE BATCH")
        title.setStyleSheet("color: #a6adc8; font-size: 11px; font-weight: bold; letter-spacing: 1px;")
        hl.addWidget(title)
        hl.addStretch()
        pl.addWidget(header)

        br1 = QHBoxLayout()
        br1.setContentsMargins(8, 8, 8, 4)
        self.scan_btn = QPushButton("🔄 Scan")
        self.scan_btn.setToolTip("Scan input/ folder")
        self.scan_btn.clicked.connect(self._scan_input_dir)
        br1.addWidget(self.scan_btn)

        self.scan_folder_btn = QPushButton("📁 Folder...")
        self.scan_folder_btn.setToolTip("Choose a folder to scan")
        self.scan_folder_btn.clicked.connect(self._scan_folder)
        br1.addWidget(self.scan_folder_btn)

        self.add_btn = QPushButton("➕ Add...")
        self.add_btn.setToolTip("Add individual files")
        self.add_btn.clicked.connect(self._add_files)
        br1.addWidget(self.add_btn)

        self.clear_btn = QPushButton("✖ Clear")
        self.clear_btn.setToolTip("Clear file list")
        self.clear_btn.clicked.connect(self._clear_list)
        br1.addWidget(self.clear_btn)
        pl.addLayout(br1)

        br2 = QHBoxLayout()
        br2.setContentsMargins(8, 0, 8, 4)
        self.select_all_btn = QPushButton("☑ All")
        self.select_all_btn.clicked.connect(self._select_all)
        br2.addWidget(self.select_all_btn)

        self.deselect_all_btn = QPushButton("☐ None")
        self.deselect_all_btn.clicked.connect(self._deselect_all)
        br2.addWidget(self.deselect_all_btn)

        br2.addStretch()

        self.recurse_chk = QCheckBox("Sub")
        self.recurse_chk.setChecked(True)
        self.recurse_chk.setToolTip("Scan subdirectories")
        br2.addWidget(self.recurse_chk)

        br2.addWidget(QLabel("Depth:"))
        self.depth_sp = QSpinBox()
        self.depth_sp.setRange(1, 99)
        self.depth_sp.setValue(10)
        self.depth_sp.setFixedWidth(50)
        br2.addWidget(self.depth_sp)
        pl.addLayout(br2)

        self.file_count_lbl = QLabel("")
        self.file_count_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; padding: 0 8px;")
        pl.addWidget(self.file_count_lbl)

        self.file_table = _BatchTableWidget(0, 4)
        self.file_table.setHorizontalHeaderLabels(["", "File", "Lang", "Status"])
        self.file_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.file_table.setEditTriggers(QTableWidget.NoEditTriggers)
        self.file_table.verticalHeader().setVisible(False)
        self.file_table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.file_table.customContextMenuRequested.connect(self._on_table_context_menu)
        hdr = self.file_table.horizontalHeader()
        hdr.setSectionResizeMode(0, QHeaderView.Fixed)
        hdr.resizeSection(0, 36)
        hdr.setSectionResizeMode(1, QHeaderView.Stretch)
        hdr.setSectionResizeMode(2, QHeaderView.Fixed)
        hdr.resizeSection(2, 70)
        hdr.setSectionResizeMode(3, QHeaderView.Fixed)
        hdr.resizeSection(3, 100)
        self.file_table.itemChanged.connect(self._on_item_changed)
        self.file_table.setStyleSheet(
            "QTableWidget { background: #181825; color: #cdd6f4; gridline-color: #313244; "
            "border: none; outline: none; } "
            "QTableWidget::item { padding: 4px 6px; border-bottom: 1px solid #11111b; } "
            "QTableWidget::item:selected { background: #89b4fa; color: #1e1e2e; } "
            "QHeaderView::section { background: #1e1e2e; color: #a6adc8; border: none; padding: 4px; font-size: 10px; }"
        )
        pl.addWidget(self.file_table, 1)

        parent_layout.addWidget(panel)

    def _build_header(self, parent_layout: QVBoxLayout) -> None:
        header = QFrame()
        header.setFixedHeight(50)
        header.setStyleSheet("QFrame { background: #181825; border-bottom: 1px solid #11111b; }")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(20, 0, 20, 0)
        title = QLabel("⌨  Junior vs Senior Dev Studio — Batch Edition")
        title.setStyleSheet("color: #cdd6f4; font-size: 16px; font-weight: bold;")
        hl.addWidget(title)
        self.path_label = QLabel("")
        self.path_label.setStyleSheet("color: #a6adc8; font-size: 11px;")
        hl.addWidget(self.path_label)
        hl.addStretch()
        hint = QLabel("Space: Play/Pause  ·  R: Reset  ·  Ctrl+E: Export  ·  Ctrl+A: Select All")
        hint.setStyleSheet("color: #585b70; font-size: 10px;")
        hl.addWidget(hint)
        parent_layout.addWidget(header)

    def _build_preview_tab(self) -> None:
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(8)
        self.preview_label = QLabel()
        self.preview_label.setAlignment(Qt.AlignCenter)
        self.preview_label.setMinimumSize(640, 360)
        self.preview_label.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.preview_label.setStyleSheet("background: #11111b; border-radius: 8px;")
        self.preview_label.setCursor(Qt.PointingHandCursor)
        self.preview_label.mousePressEvent = self._on_preview_click
        shadow = QGraphicsDropShadowEffect()
        shadow.setBlurRadius(20)
        shadow.setOffset(0, 4)
        shadow.setColor(QColor(0, 0, 0, 120))
        self.preview_label.setGraphicsEffect(shadow)
        layout.addWidget(self.preview_label, 1)

        stats_row = QHBoxLayout()
        self.time_label = QLabel("0:00 / 0:00")
        self.time_label.setStyleSheet("color: #a6e3a1; font-size: 12px; font-weight: bold; font-family: monospace;")
        stats_row.addWidget(self.time_label)
        self.stats_label = QLabel("")
        self.stats_label.setStyleSheet("color: #a6adc8; font-size: 11px; font-family: monospace;")
        stats_row.addWidget(self.stats_label)
        stats_row.addStretch()
        self.pct_label = QLabel("0%")
        self.pct_label.setStyleSheet("color: #89b4fa; font-size: 11px; font-weight: bold; font-family: monospace;")
        stats_row.addWidget(self.pct_label)
        layout.addLayout(stats_row)

        info = QHBoxLayout()
        self.info_label = QLabel("")
        self.info_label.setStyleSheet("color: #a6adc8; font-size: 11px;")
        info.addWidget(self.info_label)
        info.addStretch()
        self.duration_label = QLabel("")
        self.duration_label.setStyleSheet("color: #a6e3a1; font-size: 11px; font-weight: bold;")
        info.addWidget(self.duration_label)
        layout.addLayout(info)

        ctrl = QHBoxLayout()
        self.frame_back_btn = QPushButton("⏮")
        self.frame_back_btn.setFixedWidth(40)
        self.frame_back_btn.clicked.connect(lambda: self._seek_frame(-1))
        ctrl.addWidget(self.frame_back_btn)
        self.frame_slider = QSlider(Qt.Horizontal)
        self.frame_slider.setRange(0, 1000)
        self.frame_slider.setValue(0)
        self.frame_slider.valueChanged.connect(self._on_slider)
        ctrl.addWidget(self.frame_slider, 1)
        self.frame_fwd_btn = QPushButton("⏭")
        self.frame_fwd_btn.setFixedWidth(40)
        self.frame_fwd_btn.clicked.connect(lambda: self._seek_frame(1))
        ctrl.addWidget(self.frame_fwd_btn)
        self.loop_btn = QPushButton("🔁")
        self.loop_btn.setFixedWidth(40)
        self.loop_btn.setCheckable(True)
        self.loop_btn.toggled.connect(self._toggle_loop)
        ctrl.addWidget(self.loop_btn)
        self.play_btn = QPushButton("▶ Animate")
        self.play_btn.setFixedWidth(110)
        self.play_btn.setStyleSheet("QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 6px; } QPushButton:hover { background: #94e2d5; }")
        self.play_btn.clicked.connect(self._toggle_preview_anim)
        ctrl.addWidget(self.play_btn)
        self.fullscreen_btn = QPushButton("⛶")
        self.fullscreen_btn.setFixedWidth(40)
        self.fullscreen_btn.clicked.connect(self._toggle_fullscreen)
        ctrl.addWidget(self.fullscreen_btn)
        layout.addLayout(ctrl)

        help_label = QLabel("Space: Play/Pause  ·  ←/→: Seek frame  ·  Shift+←/→: Seek 5s  ·  L: Loop  ·  F: Fullscreen  ·  R: Reset")
        help_label.setStyleSheet("color: #585b70; font-size: 10px;")
        help_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(help_label)
        self.tabs.addTab(tab, "🎬 Preview & Export")

    def _build_settings_tab(self) -> None:
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        container = QWidget()
        cl = QVBoxLayout(container)
        cl.setSpacing(14)
        cl.setContentsMargins(16, 16, 16, 16)

        grp = QGroupBox("Appearance")
        fl = QFormLayout(grp)
        self.theme_cb = QComboBox()
        self.theme_cb.addItems(list(THEMES.keys()))
        self.theme_cb.setCurrentText("Dracula")
        fl.addRow("Theme:", self.theme_cb)

        self.font_size_auto = QCheckBox("Auto")
        self.font_size_auto.setChecked(True)
        self.font_size_sp = QSpinBox()
        self.font_size_sp.setRange(8, 72)
        self.font_size_sp.setValue(18)
        self.font_size_sp.setEnabled(False)
        self.font_size_auto.toggled.connect(self.font_size_sp.setEnabled)
        fs_row = QHBoxLayout()
        fs_row.addWidget(self.font_size_auto)
        fs_row.addWidget(self.font_size_sp)
        fl.addRow("Font Size:", fs_row)

        self.lang_cb = QComboBox()
        self.lang_cb.addItems(["Auto", "Python", "JavaScript", "TypeScript", "CFamily",
                               "CSharp", "Java", "Go", "Rust", "Ruby", "PHP", "HTML",
                               "CSS", "SQL", "Bash", "JSON", "YAML", "Markdown"])
        fl.addRow("Language:", self.lang_cb)

        self.chrome_chk = QCheckBox("Show Window Chrome")
        self.chrome_chk.setChecked(True)
        fl.addRow(self.chrome_chk)
        self.line_nums_chk = QCheckBox("Show Line Numbers")
        self.line_nums_chk.setChecked(True)
        fl.addRow(self.line_nums_chk)
        self.cursor_glow_chk = QCheckBox("Cursor Glow")
        self.cursor_glow_chk.setChecked(True)
        fl.addRow(self.cursor_glow_chk)
        self.watermark_chk = QCheckBox("Watermark")
        self.watermark_chk.setChecked(False)
        fl.addRow(self.watermark_chk)

        self.editor_padding_sp = QSpinBox()
        self.editor_padding_sp.setRange(0, 100)
        self.editor_padding_sp.setValue(24)
        self.editor_padding_sp.setSuffix("px")
        fl.addRow("Editor Padding:", self.editor_padding_sp)

        self.pane_gap_sp = QSpinBox()
        self.pane_gap_sp.setRange(0, 100)
        self.pane_gap_sp.setValue(20)
        self.pane_gap_sp.setSuffix("px")
        fl.addRow("Pane Gap:", self.pane_gap_sp)

        bg_row = QHBoxLayout()
        self.bg_edit = QLineEdit()
        self.bg_edit.setPlaceholderText("Background image (optional)")
        bg_row.addWidget(self.bg_edit)
        bg_btn = QPushButton("...")
        bg_btn.clicked.connect(self._browse_bg)
        bg_row.addWidget(bg_btn)
        fl.addRow("BG Image:", bg_row)
        cl.addWidget(grp)

        devs_row = QHBoxLayout()
        devs_row.setSpacing(12)
        _avail_fonts = QFontDatabase.families()
        _mono = ["Consolas", "JetBrains Mono", "Fira Code", "Cascadia Code",
                 "Source Code Pro", "Inconsolata", "DejaVu Sans Mono", "monospace"]
        for f in sorted(_avail_fonts):
            if f not in _mono:
                _mono.append(f)
        _font_list = [f for f in _mono if f in _avail_fonts or f == "monospace"]
        _default_font = "Consolas" if "Consolas" in _avail_fonts else "monospace"

        j_grp = QGroupBox("Junior Dev")
        j_grp.setStyleSheet("QGroupBox { color: #89b4fa; font-weight: bold; }")
        j_fl = QFormLayout(j_grp)
        self.j_font_cb = QComboBox()
        self.j_font_cb.addItems(_font_list)
        self.j_font_cb.setCurrentText(_default_font)
        j_fl.addRow("Font:", self.j_font_cb)
        self.j_wpm = QSpinBox()
        self.j_wpm.setRange(30, 300)
        self.j_wpm.setValue(90)
        j_fl.addRow("WPM:", self.j_wpm)
        self.j_pause = QDoubleSpinBox()
        self.j_pause.setRange(0, 1)
        self.j_pause.setSingleStep(0.05)
        self.j_pause.setValue(0.15)
        j_fl.addRow("Pause Freq:", self.j_pause)
        self.j_burst = QDoubleSpinBox()
        self.j_burst.setRange(0, 1)
        self.j_burst.setSingleStep(0.05)
        self.j_burst.setValue(0.15)
        j_fl.addRow("Burst Chance:", self.j_burst)
        devs_row.addWidget(j_grp)

        s_grp = QGroupBox("Senior Dev")
        s_grp.setStyleSheet("QGroupBox { color: #a6e3a1; font-weight: bold; }")
        s_fl = QFormLayout(s_grp)
        self.s_font_cb = QComboBox()
        self.s_font_cb.addItems(_font_list)
        self.s_font_cb.setCurrentText(_default_font)
        s_fl.addRow("Font:", self.s_font_cb)
        self.s_wpm = QSpinBox()
        self.s_wpm.setRange(30, 300)
        self.s_wpm.setValue(130)
        s_fl.addRow("WPM:", self.s_wpm)
        self.s_pause = QDoubleSpinBox()
        self.s_pause.setRange(0, 1)
        self.s_pause.setSingleStep(0.05)
        self.s_pause.setValue(0.05)
        s_fl.addRow("Pause Freq:", self.s_pause)
        self.s_burst = QDoubleSpinBox()
        self.s_burst.setRange(0, 1)
        self.s_burst.setSingleStep(0.05)
        self.s_burst.setValue(0.35)
        s_fl.addRow("Burst Chance:", self.s_burst)
        devs_row.addWidget(s_grp)
        cl.addLayout(devs_row)

        exp_grp = QGroupBox("Export Settings")
        el = QFormLayout(exp_grp)
        self.quality_cb = QComboBox()
        self.quality_cb.addItems(list(QUALITY_PRESETS.keys()))
        self.quality_cb.setCurrentText("Medium (1080p, 30fps)")
        el.addRow("Quality Preset:", self.quality_cb)
        self.quality_cb.currentTextChanged.connect(self._apply_quality_preset)

        self.export_format_cb = QComboBox()
        self.export_format_cb.addItems(list(EXPORT_FORMATS.keys()))
        self.export_format_cb.setCurrentText("YouTube (16:9)")
        el.addRow("Format:", self.export_format_cb)

        self.pane_layout_cb = QComboBox()
        self.pane_layout_cb.addItems([
            "Side by Side (50/50)", "Stacked (50/50)",
            "Junior Big (70/30)", "Senior Big (70/30)",
            "PIP - Senior Big (Junior Small)", "PIP - Junior Big (Senior Small)",
        ])
        el.addRow("Pane Layout:", self.pane_layout_cb)

        self.res_cb = QComboBox()
        self._populate_resolutions()
        el.addRow("Resolution:", self.res_cb)

        self.fps_sp = QSpinBox()
        self.fps_sp.setRange(10, 60)
        self.fps_sp.setValue(30)
        el.addRow("FPS:", self.fps_sp)

        self.encoder_cb = QComboBox()
        self.encoder_cb.addItems(list(ENCODERS.keys()))
        el.addRow("Encoder:", self.encoder_cb)

        self.start_pause_sp = QDoubleSpinBox()
        self.start_pause_sp.setRange(0, 10)
        self.start_pause_sp.setSingleStep(0.5)
        self.start_pause_sp.setValue(0.5)
        el.addRow("Start Pause (s):", self.start_pause_sp)

        self.end_pause_sp = QDoubleSpinBox()
        self.end_pause_sp.setRange(0, 10)
        self.end_pause_sp.setSingleStep(0.5)
        self.end_pause_sp.setValue(1.5)
        el.addRow("End Pause (s):", self.end_pause_sp)

        self.naming_edit = QLineEdit()
        self.naming_edit.setText("{name}_jr_vs_sr")
        self.naming_edit.setToolTip("Placeholders: {name} (filename), {date}, {lang}, {wpm}")
        el.addRow("Output Name:", self.naming_edit)

        self.gen_thumb_chk = QCheckBox("Generate Thumbnails (×4 JPG)")
        self.gen_thumb_chk.setChecked(True)
        el.addRow(self.gen_thumb_chk)
        self.gen_chapters_chk = QCheckBox("Generate YouTube Chapters & Description")
        self.gen_chapters_chk.setChecked(True)
        el.addRow(self.gen_chapters_chk)

        cl.addWidget(exp_grp)

        aud_grp = QGroupBox("Audio")
        al = QFormLayout(aud_grp)
        self.sound_chk = QCheckBox("Enable Typing Sounds")
        self.sound_chk.setChecked(True)
        al.addRow(self.sound_chk)
        self.sound_preset_cb = QComboBox()
        self.sound_preset_cb.addItems(list(SOUND_PRESETS.keys()))
        self.sound_preset_cb.setCurrentText("Mechanical")
        al.addRow("Preset:", self.sound_preset_cb)
        self.preset_desc = QLabel(SOUND_PRESETS["Mechanical"]["desc"])
        self.preset_desc.setStyleSheet("color: #a6adc8; font-size: 10px; font-style: italic;")
        self.preset_desc.setWordWrap(True)
        al.addRow(self.preset_desc)
        self.binaural_chk = QCheckBox("Binaural ASMR (Stereo)")
        al.addRow(self.binaural_chk)
        self.reverb_sp = QDoubleSpinBox()
        self.reverb_sp.setRange(0, 0.5)
        self.reverb_sp.setSingleStep(0.05)
        self.reverb_sp.setValue(0.10)
        al.addRow("ASMR Reverb:", self.reverb_sp)
        self.vol_sp = QSpinBox()
        self.vol_sp.setRange(0, 100)
        self.vol_sp.setValue(50)
        self.vol_sp.setSuffix("%")
        al.addRow("Volume:", self.vol_sp)
        test_row = QHBoxLayout()
        self.test_btn = QPushButton("🔊 Test Sound")
        self.test_btn.clicked.connect(self._test_sound)
        test_row.addWidget(self.test_btn)
        test_row.addStretch()
        al.addRow(test_row)
        bgm_row = QHBoxLayout()
        self.bgm_edit = QLineEdit()
        self.bgm_edit.setPlaceholderText("Background music file (mp3/wav)")
        bgm_row.addWidget(self.bgm_edit)
        bgm_btn = QPushButton("...")
        bgm_btn.clicked.connect(self._browse_bgm)
        bgm_row.addWidget(bgm_btn)
        al.addRow("BGM:", bgm_row)
        self.bgm_vol_sp = QSpinBox()
        self.bgm_vol_sp.setRange(0, 100)
        self.bgm_vol_sp.setValue(30)
        self.bgm_vol_sp.setSuffix("%")
        al.addRow("BGM Volume:", self.bgm_vol_sp)
        self.bgm_duck_sp = QSpinBox()
        self.bgm_duck_sp.setRange(0, 100)
        self.bgm_duck_sp.setValue(60)
        self.bgm_duck_sp.setSuffix("%")
        self.bgm_duck_sp.setToolTip(
            "Sidechain ducking: BGM auto-ducks when typing sounds play.\n"
            "0% = no ducking (BGM stays at full mix volume)\n"
            "60% = recommended for ASMR YouTube\n"
            "100% = max ducking (BGM almost silent during typing)")
        al.addRow("BGM Ducking:", self.bgm_duck_sp)
        cl.addWidget(aud_grp)

        kb_grp = QGroupBox("Keyboard Overlay")
        kl = QFormLayout(kb_grp)
        self.kb_chk = QCheckBox("Show Keyboard")
        self.kb_chk.setChecked(False)
        kl.addRow(self.kb_chk)
        self.kb_layout_cb = QComboBox()
        self.kb_layout_cb.addItems(list(KEYBOARD_LAYOUTS.keys()))
        kl.addRow("Layout:", self.kb_layout_cb)
        self.kb_pos_cb = QComboBox()
        self.kb_pos_cb.addItems(list(self.KB_POS_MAP.keys()))
        self.kb_pos_cb.setCurrentText("Bottom Center")
        kl.addRow("Position:", self.kb_pos_cb)
        self.kb_opacity = QDoubleSpinBox()
        self.kb_opacity.setRange(0.1, 1.0)
        self.kb_opacity.setSingleStep(0.05)
        self.kb_opacity.setValue(0.82)
        kl.addRow("Opacity:", self.kb_opacity)
        cl.addWidget(kb_grp)

        custom_grp = QGroupBox("Custom Code Input (for single preview/export)")
        cul = QVBoxLayout(custom_grp)
        j_row = QHBoxLayout()
        j_row.addWidget(QLabel("Junior Dev:"))
        j_copy_btn = QPushButton("📋 Copy")
        j_copy_btn.clicked.connect(lambda: self._copy_code('j'))
        j_row.addWidget(j_copy_btn)
        cul.addLayout(j_row)
        self.custom_junior = QPlainTextEdit()
        self.custom_junior.setPlaceholderText("Code loads here when you click a file...")
        self.custom_junior.setMaximumHeight(100)
        self.custom_junior.setStyleSheet("QPlainTextEdit { background: #11111b; color: #cdd6f4; font-family: monospace; font-size: 11px; border: 1px solid #89b4fa; border-radius: 4px; }")
        cul.addWidget(self.custom_junior)
        s_row = QHBoxLayout()
        s_row.addWidget(QLabel("Senior Dev:"))
        s_copy_btn = QPushButton("📋 Copy")
        s_copy_btn.clicked.connect(lambda: self._copy_code('s'))
        s_row.addWidget(s_copy_btn)
        cul.addLayout(s_row)
        self.custom_senior = QPlainTextEdit()
        self.custom_senior.setPlaceholderText("Paste Senior Dev code here (or copy from Junior & edit)...")
        self.custom_senior.setMaximumHeight(100)
        self.custom_senior.setStyleSheet("QPlainTextEdit { background: #11111b; color: #cdd6f4; font-family: monospace; font-size: 11px; border: 1px solid #a6e3a1; border-radius: 4px; }")
        cul.addWidget(self.custom_senior)
        load_row = QHBoxLayout()
        self.load_custom_btn = QPushButton("Load Custom Code")
        self.load_custom_btn.clicked.connect(self._load_custom)
        load_row.addWidget(self.load_custom_btn)
        load_row.addStretch()
        self.use_custom_chk = QCheckBox("Use custom code for batch export")
        self.use_custom_chk.setToolTip("If checked, batch export uses the custom code instead of file contents")
        load_row.addWidget(self.use_custom_chk)
        cul.addLayout(load_row)
        cl.addWidget(custom_grp)
        cl.addStretch()
        scroll.setWidget(container)
        self.tabs.addTab(scroll, "⚙ Settings")
        self.j_highlighter = PythonHighlighter(self.custom_junior.document())
        self.s_highlighter = PythonHighlighter(self.custom_senior.document())

    def _build_controls(self, parent_layout: QVBoxLayout) -> None:
        bar = QFrame()
        bar.setFixedHeight(56)
        bar.setStyleSheet("QFrame { background: #181825; border-top: 1px solid #11111b; }")
        bl = QHBoxLayout(bar)
        bl.setContentsMargins(20, 10, 20, 10)
        bl.setSpacing(10)

        self.play_pause_btn = QPushButton("▶ Play")
        self.play_pause_btn.setFixedSize(90, 36)
        self.play_pause_btn.setCursor(Qt.PointingHandCursor)
        self.play_pause_btn.setStyleSheet("QPushButton { background: #89b4fa; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; } QPushButton:hover { background: #74c7ec; }")
        self.play_pause_btn.clicked.connect(self._toggle_preview_anim)
        bl.addWidget(self.play_pause_btn)

        self.reset_btn = QPushButton("⟲ Reset")
        self.reset_btn.setFixedSize(80, 36)
        self.reset_btn.setCursor(Qt.PointingHandCursor)
        self.reset_btn.setStyleSheet("QPushButton { background: #45475a; color: #cdd6f4; border: none; border-radius: 6px; } QPushButton:hover { background: #585b70; }")
        self.reset_btn.clicked.connect(self._reset_preview)
        bl.addWidget(self.reset_btn)

        bl.addStretch()

        self.batch_progress_lbl = QLabel("")
        self.batch_progress_lbl.setStyleSheet("color: #a6adc8; font-size: 11px;")
        bl.addWidget(self.batch_progress_lbl)
        self.progress_bar = QProgressBar()
        self.progress_bar.setFixedWidth(200)
        self.progress_bar.setVisible(False)
        self.progress_bar.setFormat("%v / %m  (%p%)")
        bl.addWidget(self.progress_bar)

        self.export_btn = QPushButton("🎬 Export Checked")
        self.export_btn.setFixedHeight(36)
        self.export_btn.setCursor(Qt.PointingHandCursor)
        self.export_btn.setStyleSheet("QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 0 16px; } QPushButton:hover { background: #94e2d5; }")
        self.export_btn.clicked.connect(self._start_export)
        bl.addWidget(self.export_btn)

        self.open_output_btn = QPushButton("📂 Output")
        self.open_output_btn.setFixedHeight(36)
        self.open_output_btn.setToolTip("Open output folder")
        self.open_output_btn.clicked.connect(self._open_output_folder)
        bl.addWidget(self.open_output_btn)

        self.open_last_btn = QPushButton("▶ Last")
        self.open_last_btn.setFixedHeight(36)
        self.open_last_btn.setEnabled(False)
        self.open_last_btn.setToolTip("Play last exported video")
        self.open_last_btn.clicked.connect(self._open_last_output)
        bl.addWidget(self.open_last_btn)

        self.cancel_btn = QPushButton("✖ Cancel")
        self.cancel_btn.setFixedHeight(36)
        self.cancel_btn.setEnabled(False)
        self.cancel_btn.clicked.connect(self._cancel_export)
        bl.addWidget(self.cancel_btn)

        parent_layout.addWidget(bar)

    def _scan_input_dir(self) -> None:
        self._scan_directory(str(INPUT_DIR))

    def _scan_folder(self) -> None:
        folder = QFileDialog.getExistingDirectory(self, "Select Folder to Scan", self._input_dir)
        if folder:
            self._input_dir = folder
            self._scan_directory(folder)

    def _scan_directory(self, root_dir: str) -> None:
        self._items.clear()
        self._checkbox_anchor = None
        if not os.path.isdir(root_dir):
            self.statusBar().showMessage(f"Folder not found: {root_dir}")
            self._refresh_table()
            return
        max_depth = self.depth_sp.value() if self.recurse_chk.isChecked() else 1
        found: List[FileItem] = []
        for dirpath, dirnames, filenames in os.walk(root_dir):
            rel = os.path.relpath(dirpath, root_dir)
            depth = 1 if rel == "." else rel.count(os.sep) + 2
            if depth > max_depth:
                dirnames.clear()
                continue
            dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS and not d.startswith(".")]
            for fname in sorted(filenames):
                ext = os.path.splitext(fname)[1].lower()
                if ext in SUPPORTED_EXTENSIONS:
                    found.append(FileItem(path=os.path.join(dirpath, fname)))
        self._items = found
        self._item_paths = {it.path for it in found}
        self._refresh_table()
        rn = f" (depth ≤ {max_depth})" if self.recurse_chk.isChecked() else " (top-level only)"
        self.file_count_lbl.setText(f"{len(self._items)} file(s) found{rn}")
        self.statusBar().showMessage(f"Found {len(self._items)} code file(s) in {root_dir}{rn}")
        self.path_label.setText(f"📂 {root_dir}")

    def _add_files(self) -> None:
        es = " ".join(f"*{e}" for e in sorted(SUPPORTED_EXTENSIONS))
        paths, _ = QFileDialog.getOpenFileNames(self, "Select Code Files", "", f"Code Files ({es});;All Files (*)")
        for p in paths:
            if p not in self._item_paths:
                self._items.append(FileItem(path=p, checked=True))
                self._item_paths.add(p)
        self._refresh_table()

    def _clear_list(self) -> None:
        self._items.clear()
        self._item_paths.clear()
        self._checkbox_anchor = None
        self._refresh_table()
        self._invalidate_and_schedule()

    def _select_all(self) -> None:
        for it in self._items:
            it.checked = True
        self._checkbox_anchor = None
        self._refresh_table()

    def _deselect_all(self) -> None:
        for it in self._items:
            it.checked = False
        self._checkbox_anchor = None
        self._refresh_table()

    def _on_item_changed(self, item: QTableWidgetItem) -> None:
        row = item.row()
        col = item.column()
        if col == 0 and 0 <= row < len(self._items):
            ns = (item.checkState() == Qt.CheckState.Checked)
            mods = QApplication.keyboardModifiers()
            if mods & Qt.ShiftModifier and self._checkbox_anchor is not None and self._checkbox_anchor != row:
                a = self._checkbox_anchor
                lo, hi = min(a, row), max(a, row)
                self.file_table.blockSignals(True)
                for i in range(lo, hi + 1):
                    self._items[i].checked = ns
                    ci = self.file_table.item(i, 0)
                    if ci is not None:
                        ci.setCheckState(Qt.CheckState.Checked if ns else Qt.CheckState.Unchecked)
                self.file_table.blockSignals(False)
            else:
                self._items[row].checked = ns
                self._checkbox_anchor = row
            self._invalidate_and_schedule()

    def _on_table_context_menu(self, pos) -> None:
        item = self.file_table.itemAt(pos)
        if not item:
            return
        row = item.row()
        if row >= len(self._items):
            return
        menu = QMenu(self)
        ea = menu.addAction("🎬 Export This File Only")
        ca = menu.addAction("📋 Load for Preview")
        action = menu.exec_(self.file_table.viewport().mapToGlobal(pos))
        if action == ea:
            for it in self._items:
                it.checked = False
            self._items[row].checked = True
            self._checkbox_anchor = None
            self._refresh_table()
            self._start_export()
        elif action == ca:
            self._load_file_for_preview(self._items[row].path)

    def _refresh_table(self) -> None:
        self.file_table.blockSignals(True)
        self.file_table.setRowCount(len(self._items))
        for i, item in enumerate(self._items):
            chk = QTableWidgetItem()
            chk.setFlags(Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsEnabled)
            chk.setCheckState(Qt.CheckState.Checked if item.checked else Qt.CheckState.Unchecked)
            self.file_table.setItem(i, 0, chk)
            try:
                rel = os.path.relpath(item.path, self._input_dir)
                dp = rel if not rel.startswith("..") else os.path.basename(item.path)
            except ValueError:
                dp = os.path.basename(item.path)
            pi = QTableWidgetItem(dp)
            pi.setToolTip(item.path)
            self.file_table.setItem(i, 1, pi)
            ext = os.path.splitext(item.path)[1].lower()
            lang = EXT_TO_LANGUAGE.get(ext, "Text")
            self.file_table.setItem(i, 2, QTableWidgetItem(lang))
            si = QTableWidgetItem(item.status)
            if "Done" in item.status:
                si.setForeground(QColor("#a6e3a1"))
            elif item.status == "Failed":
                si.setForeground(QColor("#ff5555"))
            elif item.status == "Rendering":
                si.setForeground(QColor("#89b4fa"))
            self.file_table.setItem(i, 3, si)
        self.file_table.blockSignals(False)

    def _load_file_for_preview(self, path: str) -> None:
        if not path or not os.path.isfile(path):
            return
        try:
            if path.lower().endswith('.json'):
                with open(path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                if isinstance(data, dict) and 'junior' in data and 'senior' in data:
                    self.custom_junior.setPlainText(data['junior'])
                    self.custom_senior.setPlainText(data['senior'])
                    self._current_junior_code = data['junior']
                    self._current_senior_code = data['senior']
                    self._current_name = os.path.basename(path).replace('.json', '')
                    self._invalidate_and_schedule()
                    self.statusBar().showMessage(f"Loaded snippet pair: {self._current_name}")
                    return
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
            self.custom_junior.setPlainText(content)
            self.custom_senior.setPlainText(content)
            self._current_junior_code = content
            self._current_senior_code = content
            self._current_name = os.path.basename(path)
            self._invalidate_and_schedule()
            self.statusBar().showMessage(f"Loaded: {self._current_name}")
        except Exception as e:
            self.statusBar().showMessage(f"Error: {e}")

    def _check_disk_space(self, output_dir: str, estimated_mb: int = 2000) -> bool:
        try:
            usage = shutil.disk_usage(output_dir)
            free_mb = usage.free / (1024 * 1024)
            if free_mb < estimated_mb:
                reply = QMessageBox.warning(
                    self, "Low Disk Space",
                    f"Only {free_mb:.0f} MB free.\nThis batch may need ~{estimated_mb} MB.\nContinue?",
                    QMessageBox.Yes | QMessageBox.No, QMessageBox.No
                )
                return reply == QMessageBox.Yes
        except Exception:
            pass
        return True

    def _start_export(self) -> None:
        if shutil.which("ffmpeg") is None:
            QMessageBox.critical(self, "FFmpeg Not Found", "FFmpeg is not installed or not on PATH.")
            return

        checked = [it for it in self._items if it.checked]
        if not checked:
            if not self._current_junior_code or not self._current_senior_code:
                QMessageBox.information(self, "Nothing Selected", "Check files or load custom code.")
                return
            self._export_single()
            return

        if not self._check_disk_space(str(OUTPUT_DIR)):
            return

        for it in checked:
            it.status = "Pending"
            it.output_path = None
            it.error = None
        self._refresh_table()
        self._export_queue = list(checked)
        self._batch_total = len(checked)
        self._batch_done = 0
        self.progress_bar.setVisible(True)
        self.progress_bar.setRange(0, self._batch_total)
        self.progress_bar.setValue(0)
        self.export_btn.setEnabled(False)
        self.cancel_btn.setEnabled(True)
        self._export_next_batch_item()

    def _export_next_batch_item(self) -> None:
        if not self._export_queue:
            self.export_btn.setEnabled(True)
            self.cancel_btn.setEnabled(False)
            done = sum(1 for it in self._items if "Done" in it.status)
            failed = sum(1 for it in self._items if it.status == "Failed")
            msg = f"Batch complete: {done} done"
            if failed:
                msg += f", {failed} failed"
            self.statusBar().showMessage(msg, 5000)
            self.batch_progress_lbl.setText("")
            return

        item = self._export_queue.pop(0)
        item.status = "Rendering"
        self._refresh_table()
        self.batch_progress_lbl.setText(f"Exporting {self._batch_done + 1}/{self._batch_total}: {os.path.basename(item.path)}")

        junior_code, senior_code, name = self._load_codes_for_item(item)
        if not junior_code or not senior_code:
            item.status = "Failed"
            item.error = "Could not load code"
            self._refresh_table()
            self._batch_done += 1
            self.progress_bar.setValue(self._batch_done)
            self._export_next_batch_item()
            return

        lang_text = self.lang_cb.currentText()
        if lang_text == "Auto":
            ext = os.path.splitext(item.path)[1].lower()
            language = EXT_TO_LANGUAGE.get(ext, "Text")
        else:
            language = lang_text

        cfg = (ExportConfigBuilder()
               .junior_code(junior_code)
               .senior_code(senior_code)
               .name(name)
               .fmt(self.export_format_cb.currentText())
               .res(self.res_cb.currentText())
               .theme(self.theme_cb.currentText())
               .j_font(self.j_font_cb.currentText())
               .s_font(self.s_font_cb.currentText())
               .font_size_auto(self.font_size_auto.isChecked())
               .font_size(self.font_size_sp.value())
               .chrome(self.chrome_chk.isChecked())
               .ln(self.line_nums_chk.isChecked())
               .cursor_glow(self.cursor_glow_chk.isChecked())
               .watermark(self.watermark_chk.isChecked())
               .bg_image_path(self._bg_image_path)
               .show_kb(self.kb_chk.isChecked())
               .kb_layout(self.kb_layout_cb.currentText())
               .kb_pos(self.KB_POS_MAP.get(self.kb_pos_cb.currentText(), "bottom_center"))
               .kb_op(self.kb_opacity.value())
               .j_wpm(self.j_wpm.value())
               .j_pause(self.j_pause.value())
               .j_burst(self.j_burst.value())
               .s_wpm(self.s_wpm.value())
               .s_pause(self.s_pause.value())
               .s_burst(self.s_burst.value())
               .start_pause(self.start_pause_sp.value())
               .end_pause(self.end_pause_sp.value())
               .lang(language)
               .pane_layout(self.pane_layout_cb.currentText())
               .pad(self.editor_padding_sp.value())
               .gap(self.pane_gap_sp.value())
               .build())

        template = self.naming_edit.text().strip() or "{name}_jr_vs_sr"
        base = os.path.splitext(os.path.basename(item.path))[0]
        date_str = datetime.now().strftime("%Y%m%d")
        out_name = template.format(name=base, date=date_str, lang=language, wpm=self.j_wpm.value())
        out_name = re.sub(r'[<>:"/\\|?*]', '_', out_name)
        fmt = self.export_format_cb.currentText()
        suffix = "_shorts" if "Shorts" in fmt else ""
        output_path = os.path.join(str(OUTPUT_DIR), f"{out_name}{suffix}.mp4")

        sound_params = (self.sound_preset_cb.currentText(), self.binaural_chk.isChecked(),
                        self.reverb_sp.value()) if self.sound_chk.isChecked() else None
        bgm_path = self.bgm_edit.text().strip()

        self._exporter = VideoExporter(
            cfg, output_path, self.fps_sp.value(), sound_params,
            self.vol_sp.value() / 100.0, self.encoder_cb.currentText(),
            bgm_path if bgm_path else None,
            self.bgm_vol_sp.value() / 100.0,
            self.bgm_duck_sp.value() / 100.0
        )
        self._exporter.progress.connect(self._on_export_progress)
        self._exporter.status.connect(self.statusBar().showMessage)
        self._exporter.finished_ok.connect(lambda p, it=item: self._on_batch_item_done(it, p))
        self._exporter.error.connect(lambda e, it=item: self._on_batch_item_failed(it, e))
        self._exporter.start()

    def _load_codes_for_item(self, item: FileItem) -> Tuple[str, str, str]:
        if self.use_custom_chk.isChecked() and self._current_junior_code and self._current_senior_code:
            return self._current_junior_code, self._current_senior_code, os.path.basename(item.path)
        try:
            if item.path.lower().endswith('.json'):
                with open(item.path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                if isinstance(data, dict) and 'junior' in data and 'senior' in data:
                    return data['junior'], data['senior'], os.path.basename(item.path).replace('.json', '')
            with open(item.path, 'r', encoding='utf-8') as f:
                content = f.read()
            return content, content, os.path.basename(item.path)
        except Exception as e:
            log.error("Failed to load %s: %s", item.path, e)
            return "", "", os.path.basename(item.path)

    def _on_batch_item_done(self, item: FileItem, path: str) -> None:
        item.status = "Done"
        item.output_path = path
        self.open_last_btn.setEnabled(True)
        self._batch_done += 1
        self.progress_bar.setValue(self._batch_done)

        if self.gen_thumb_chk.isChecked():
            try:
                self._generate_thumbnails(path)
            except Exception as e:
                log.warning("Thumbnail generation failed: %s", e)
        if self.gen_chapters_chk.isChecked():
            try:
                self._generate_chapters(item, path)
            except Exception as e:
                log.warning("Chapters generation failed: %s", e)

        self._refresh_table()
        self._exporter = None
        self._export_next_batch_item()

    def _on_batch_item_failed(self, item: FileItem, err: str) -> None:
        item.status = "Failed"
        item.error = err
        self._batch_done += 1
        self.progress_bar.setValue(self._batch_done)
        self._refresh_table()
        self._exporter = None
        self._export_next_batch_item()

    def _export_single(self) -> None:
        if not self._current_junior_code or not self._current_senior_code:
            QMessageBox.information(self, "No Code", "Please load a file or paste custom code.")
            return
        if self._audio_workers:
            for t in list(self._audio_workers):
                t.quit()
                t.wait(3000)
            self._audio_workers.clear()
        self._stop_preview_anim()

        lang_text = self.lang_cb.currentText()
        language = self._detect_language(self._current_name, self._current_junior_code) if lang_text == "Auto" else lang_text
        cfg = (ExportConfigBuilder()
               .junior_code(self._current_junior_code)
               .senior_code(self._current_senior_code)
               .name(self._current_name)
               .fmt(self.export_format_cb.currentText())
               .res(self.res_cb.currentText())
               .theme(self.theme_cb.currentText())
               .j_font(self.j_font_cb.currentText())
               .s_font(self.s_font_cb.currentText())
               .font_size_auto(self.font_size_auto.isChecked())
               .font_size(self.font_size_sp.value())
               .chrome(self.chrome_chk.isChecked())
               .ln(self.line_nums_chk.isChecked())
               .cursor_glow(self.cursor_glow_chk.isChecked())
               .watermark(self.watermark_chk.isChecked())
               .bg_image_path(self._bg_image_path)
               .show_kb(self.kb_chk.isChecked())
               .kb_layout(self.kb_layout_cb.currentText())
               .kb_pos(self.KB_POS_MAP.get(self.kb_pos_cb.currentText(), "bottom_center"))
               .kb_op(self.kb_opacity.value())
               .j_wpm(self.j_wpm.value())
               .j_pause(self.j_pause.value())
               .j_burst(self.j_burst.value())
               .s_wpm(self.s_wpm.value())
               .s_pause(self.s_pause.value())
               .s_burst(self.s_burst.value())
               .start_pause(self.start_pause_sp.value())
               .end_pause(self.end_pause_sp.value())
               .lang(language)
               .pane_layout(self.pane_layout_cb.currentText())
               .pad(self.editor_padding_sp.value())
               .gap(self.pane_gap_sp.value())
               .build())
        fmt = self.export_format_cb.currentText()
        suffix = "_shorts" if "Shorts" in fmt else ""
        base = self._current_name.replace(' ', '_').lower() if self._current_name else "comparison"
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        default_name = f"{base}{suffix}_{timestamp}.mp4"
        default_path = os.path.join(str(OUTPUT_DIR), default_name)
        path, _ = QFileDialog.getSaveFileName(self, "Export Video", default_path, "MP4 Video (*.mp4)")
        if not path:
            return
        if not path.lower().endswith('.mp4'):
            path += '.mp4'
        sound_params = (self.sound_preset_cb.currentText(), self.binaural_chk.isChecked(),
                        self.reverb_sp.value()) if self.sound_chk.isChecked() else None
        bgm_path = self.bgm_edit.text().strip()
        self.progress_bar.setVisible(True)
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.export_btn.setEnabled(False)
        self.cancel_btn.setEnabled(True)
        self._exporter = VideoExporter(
            cfg, path, self.fps_sp.value(), sound_params,
            self.vol_sp.value() / 100.0, self.encoder_cb.currentText(),
            bgm_path if bgm_path else None,
            self.bgm_vol_sp.value() / 100.0,
            self.bgm_duck_sp.value() / 100.0
        )
        self._exporter.progress.connect(self._on_export_progress)
        self._exporter.status.connect(self.statusBar().showMessage)
        self._exporter.finished_ok.connect(lambda p: self._on_single_export_done(p))
        self._exporter.error.connect(lambda e: self._on_single_export_error(e))
        self._exporter.start()

    def _on_single_export_done(self, path: str) -> None:
        self.progress_bar.setVisible(False)
        self.export_btn.setEnabled(True)
        self.cancel_btn.setEnabled(False)
        self._exporter = None
        self.statusBar().showMessage(f"Export complete! → {path}", 5000)
        QMessageBox.information(self, "Export Complete", f"Video saved to:\n{path}")

    def _on_single_export_error(self, err: str) -> None:
        self.progress_bar.setVisible(False)
        self.export_btn.setEnabled(True)
        self.cancel_btn.setEnabled(False)
        self._exporter = None
        QMessageBox.warning(self, "Export Failed", err)

    def _cancel_export(self) -> None:
        if self._exporter:
            self._exporter.cancel()
            self.statusBar().showMessage("Cancelling...")

    def _on_export_progress(self, val: int) -> None:
        self.progress_bar.setValue(val)

    def _generate_thumbnails(self, video_path: str) -> None:
        base = os.path.splitext(video_path)[0]
        mp = _build_panes_from_config(self._exporter.config)
        for i, pct in enumerate([0.25, 0.50, 0.75, 0.95]):
            tp = f"{base}_thumb_{i+1}.jpg"
            t = mp.duration() * pct
            state = mp.compute_state(t)
            qimg = mp.render_frame(t, precomputed_state=state)
            qimg.save(tp, "JPG", 95)

    def _generate_chapters(self, item: FileItem, video_path: str) -> None:
        base = os.path.splitext(video_path)[0]
        cp = base + "_chapters.txt"
        junior_code = item.junior_code or ""
        if not junior_code:
            try:
                with open(item.path, 'r', encoding='utf-8') as f:
                    junior_code = f.read()
            except Exception:
                return
        ext = os.path.splitext(item.path)[1].lower()
        lang = EXT_TO_LANGUAGE.get(ext, "Text")
        markers = Tokenizer.find_structural_markers(junior_code, lang)
        jp = TypingProfile(name="Junior", wpm=self.j_wpm.value(), pause_freq=self.j_pause.value(),
                           burst_chance=self.j_burst.value(), start_pause=self.start_pause_sp.value(),
                           end_pause=self.end_pause_sp.value())
        animator = TypingAnimator(junior_code, jp, seed=42)
        chapters = []
        for code_offset, _, label in markers:
            for ts, idx, ch, _ in animator.timeline:
                if idx == code_offset:
                    chapters.append((ts + animator.profile.start_pause, label))
                    break
        chapters = [(0.0, "Intro")] + [c for c in chapters if c[0] > 0]
        dur = animator.duration()
        if not chapters or chapters[-1][0] < dur - 5:
            chapters.append((dur - 2.0, "Outro"))
        filtered = []
        last_ts = -100
        for ts, label in chapters:
            if ts - last_ts >= 10 or ts == 0:
                filtered.append((ts, label))
                last_ts = ts

        def _fmt(s: float) -> str:
            if s < 3600:
                return f"{int(s // 60)}:{int(s % 60):02d}"
            return f"{int(s // 3600)}:{int((s % 3600) // 60):02d}:{int(s % 60):02d}"

        ct = "\n".join(f"{_fmt(ts)} {label}" for ts, label in filtered)
        with open(cp, "w", encoding="utf-8") as f:
            f.write(ct)

        dp = base + "_description.txt"
        title = os.path.splitext(os.path.basename(video_path))[0].replace("_", " ").title()
        desc = f"""{title}

Junior vs Senior Developer code typing comparison.
Watch how a junior dev types vs a senior dev on the same code!

Timestamps:
{ct}

#coding #programming #typingtutorial #code #asmr #juniorvssenior

---
Generated by Junior vs Senior Dev Studio
"""
        with open(dp, "w", encoding="utf-8") as f:
            f.write(desc)

    def _open_output_folder(self) -> None:
        path = os.path.abspath(str(OUTPUT_DIR))
        if platform.system() == "Windows":
            os.startfile(path)
        elif platform.system() == "Darwin":
            subprocess.run(["open", path])
        else:
            subprocess.run(["xdg-open", path])

    def _open_last_output(self) -> None:
        for it in reversed(self._items):
            if it.output_path and os.path.exists(it.output_path):
                if platform.system() == "Windows":
                    os.startfile(it.output_path)
                elif platform.system() == "Darwin":
                    subprocess.run(["open", it.output_path])
                else:
                    subprocess.run(["xdg-open", it.output_path])
                return
        QMessageBox.information(self, "No Output", "No completed exports found.")

    def _populate_resolutions(self) -> None:
        fmt = self.export_format_cb.currentText()
        self.res_cb.clear()
        for res in EXPORT_FORMATS.get(fmt, EXPORT_FORMATS["YouTube (16:9)"])["resolutions"]:
            self.res_cb.addItem(res)

    def _apply_quality_preset(self, preset_name: str) -> None:
        if not hasattr(self, 'export_format_cb'):
            return
        preset = QUALITY_PRESETS.get(preset_name)
        if not preset:
            return
        fmt = self.export_format_cb.currentText()
        if preset['res'] in EXPORT_FORMATS.get(fmt, {}).get('resolutions', {}):
            idx = self.res_cb.findText(preset['res'])
            if idx >= 0:
                self.res_cb.setCurrentIndex(idx)
        self.fps_sp.setValue(preset['fps'])
        idx = self.encoder_cb.findText(preset['encoder'])
        if idx >= 0:
            self.encoder_cb.setCurrentIndex(idx)

    def _detect_language(self, filename: str, code: str) -> str:
        ext = os.path.splitext(filename)[1].lower()
        if ext in EXT_TO_LANGUAGE:
            return EXT_TO_LANGUAGE[ext]
        stripped = code.lstrip()
        if stripped.startswith("<?php"):
            return "PHP"
        if stripped.startswith("<!DOCTYPE html") or "<html" in stripped[:100]:
            return "HTML"
        if "func " in code or "package main" in code:
            return "Go"
        if "fn " in code or "impl " in code:
            return "Rust"
        if "def " in code and ":" in code:
            return "Python"
        if "function " in code or "const " in code or "var " in code:
            return "JavaScript"
        if "#include" in code or "std::" in code:
            return "CFamily"
        return "Text"

    def _connect_signals(self) -> None:
        self.export_format_cb.currentTextChanged.connect(self._populate_resolutions)
        self.sound_preset_cb.currentTextChanged.connect(
            lambda t: self.preset_desc.setText(SOUND_PRESETS.get(t, {}).get("desc", "")))
        watched_widgets = [
            self.theme_cb, self.j_font_cb, self.s_font_cb, self.font_size_sp,
            self.chrome_chk, self.line_nums_chk, self.cursor_glow_chk,
            self.watermark_chk, self.export_format_cb, self.res_cb, self.fps_sp,
            self.encoder_cb, self.start_pause_sp, self.end_pause_sp,
            self.j_wpm, self.j_pause, self.j_burst, self.s_wpm, self.s_pause,
            self.s_burst, self.sound_chk, self.sound_preset_cb, self.binaural_chk,
            self.reverb_sp, self.vol_sp, self.kb_chk, self.kb_layout_cb,
            self.kb_pos_cb, self.kb_opacity, self.font_size_auto, self.lang_cb,
            self.pane_layout_cb, self.editor_padding_sp, self.pane_gap_sp,
            self.bgm_vol_sp, self.bgm_duck_sp,
        ]
        for w in watched_widgets:
            if hasattr(w, 'currentTextChanged'):
                w.currentTextChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'valueChanged'):
                w.valueChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'stateChanged'):
                w.stateChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'toggled'):
                w.toggled.connect(self._invalidate_and_schedule)
        self.bg_edit.textChanged.connect(self._update_bg_path)

        def _bind(key, cb):
            s = QShortcut(QKeySequence(key), self)
            s.activated.connect(cb)
            self._shortcuts.append(s)

        _bind(Qt.Key_Space, self._toggle_preview_anim)
        _bind("R", self._reset_preview)
        _bind("Ctrl+E", self._start_export)
        _bind("Ctrl+A", self._select_all)
        _bind("Ctrl+Shift+A", self._deselect_all)
        _bind(Qt.Key_Left, lambda: self._seek_frame(-1))
        _bind(Qt.Key_Right, lambda: self._seek_frame(1))
        _bind("Shift+Left", lambda: self._seek_preview(-5))
        _bind("Shift+Right", lambda: self._seek_preview(5))
        _bind("L", lambda: self.loop_btn.click())
        _bind("F", self._toggle_fullscreen)
        _bind(Qt.Key_Home, self._seek_start)
        _bind(Qt.Key_End, self._seek_end)

    def _update_bg_path(self, text: str) -> None:
        self._bg_image_path = text
        self._invalidate_and_schedule()

    def _seek_start(self) -> None:
        self._stop_preview_anim()
        self._preview_progress = 0.0
        self._update_preview()

    def _seek_end(self) -> None:
        self._stop_preview_anim()
        self._preview_progress = 1.0
        self._update_preview()

    def _invalidate_and_schedule(self, *_) -> None:
        if self._loading_settings:
            return
        self._cached_key = None
        self._cached_mp = None
        self._cached_panes = []
        self._preview_scratch = None
        if not hasattr(self, '_sched_timer'):
            self._sched_timer = QTimer(self)
            self._sched_timer.setSingleShot(True)
            self._sched_timer.setInterval(300)
            self._sched_timer.timeout.connect(self._update_preview)
        self._sched_timer.start()

    def _load_custom(self) -> None:
        j = self.custom_junior.toPlainText().strip()
        s = self.custom_senior.toPlainText().strip()
        if not j or not s:
            QMessageBox.warning(self, "Empty Code", "Please enter code for both developers.")
            return
        self._current_junior_code = j
        self._current_senior_code = s
        self._current_name = "Custom Snippet"
        self._invalidate_and_schedule()
        self.statusBar().showMessage("Loaded custom snippet.")

    def _copy_code(self, dev_type: str) -> None:
        text = self.custom_junior.toPlainText() if dev_type == 'j' else self.custom_senior.toPlainText()
        if text:
            QApplication.clipboard().setText(text)
            self.statusBar().showMessage("Code copied to clipboard!", 2000)

    def _browse_bg(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Background Image", "", "Images (*.png *.jpg *.jpeg *.bmp)")
        if path:
            self._bg_image_path = path
            self.bg_edit.setText(path)

    def _browse_bgm(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Background Music", "", "Audio Files (*.mp3 *.wav *.ogg *.flac *.m4a)")
        if path:
            self.bgm_edit.setText(path)

    def _start_audio_worker(self, timestamps: List[Tuple[float, str]], volume: float,
                            filepath: Optional[str] = None, callback: Optional[Callable] = None,
                            error_callback: Optional[Callable] = None,
                            bgm_path: Optional[str] = None, bgm_volume: float = 0.3,
                            bgm_duck: float = 0.6) -> None:
        sound_params = (self.sound_preset_cb.currentText(), self.binaural_chk.isChecked(), self.reverb_sp.value())
        worker = AudioWorker(sound_params, timestamps, volume, filepath,
                             bgm_path, bgm_volume, bgm_duck)
        thread = QThread()
        worker.moveToThread(thread)
        thread.started.connect(worker.run)
        if callback:
            worker.finished.connect(callback)
        if error_callback:
            worker.error.connect(error_callback)
        else:
            worker.error.connect(lambda e: QMessageBox.warning(self, "Audio Error", e))
        worker.finished.connect(thread.quit)
        worker.error.connect(thread.quit)
        thread.finished.connect(worker.deleteLater)
        thread.finished.connect(lambda t=thread: self._on_audio_thread_finished(t))
        self._audio_workers.append(thread)
        thread.start()

    def _on_audio_thread_finished(self, thread: QThread) -> None:
        thread.wait(2000)
        if thread in self._audio_workers:
            self._audio_workers.remove(thread)
        thread.deleteLater()

    def _test_sound(self) -> None:
        vol = self.vol_sp.value() / 100.0
        ts: List[Tuple[float, str]] = []
        t = 0.0
        for ch in "hello world\n":
            ts.append((t, ch))
            t += 0.25 if ch == "\n" else (0.12 if ch == " " else 0.08)
        self.statusBar().showMessage("Generating test sound...")
        self.test_btn.setEnabled(False)

        def on_finished(data):
            self.test_btn.setEnabled(True)
            if data and isinstance(data, bytes):
                self._play_audio_bytes(data, vol)
                self.statusBar().showMessage("Playing test sound...", 3000)
            else:
                self.statusBar().showMessage("No audio generated.", 3000)

        def on_error(err):
            self.test_btn.setEnabled(True)
            QMessageBox.warning(self, "Audio Error", err)

        self._start_audio_worker(ts, vol, callback=on_finished, error_callback=on_error)

    def _build_panes(self) -> MultiPaneRenderer:
        fmt = self.export_format_cb.currentText()
        fmt_data = EXPORT_FORMATS.get(fmt, EXPORT_FORMATS["YouTube (16:9)"])
        res_name = self.res_cb.currentText()
        w, h = fmt_data["resolutions"].get(res_name, (1920, 1080))
        theme_name = self.theme_cb.currentText()
        theme = THEMES[theme_name]
        pad = self.editor_padding_sp.value()
        chrome = self.chrome_chk.isChecked()
        ln = self.line_nums_chk.isChecked()
        j_font = self.j_font_cb.currentText()
        s_font = self.s_font_cb.currentText()
        show_kb = self.kb_chk.isChecked()
        kb_layout = self.kb_layout_cb.currentText()
        kb_pos = self.KB_POS_MAP.get(self.kb_pos_cb.currentText(), "bottom_center")
        kb_op = self.kb_opacity.value()
        junior_code = self._current_junior_code or _SAMPLE_CODE
        senior_code = self._current_senior_code or _SAMPLE_CODE
        jp = TypingProfile(name="Junior Dev", wpm=self.j_wpm.value(), pause_freq=self.j_pause.value(),
                           burst_chance=self.j_burst.value(), start_pause=self.start_pause_sp.value(),
                           end_pause=self.end_pause_sp.value(), error_chance=0.04)
        sp = TypingProfile(name="Senior Dev", wpm=self.s_wpm.value(), pause_freq=self.s_pause.value(),
                           burst_chance=self.s_burst.value(), start_pause=self.start_pause_sp.value(),
                           end_pause=self.end_pause_sp.value(), error_chance=0.01)
        pane_layout = self.pane_layout_cb.currentText()
        gap = self.pane_gap_sp.value()
        panes: List[Tuple[CodeRenderer, TypingAnimator]] = []
        for i, (code, profile, title, accent_key) in enumerate([
            (junior_code, jp, f"👶 Junior Dev — {self._current_name}", "junior_accent"),
            (senior_code, sp, f"🧓 Senior Dev — {self._current_name}", "senior_accent")
        ]):
            match pane_layout:
                case "Side by Side (50/50)": pw, ph = (w - gap) // 2, h
                case "Stacked (50/50)": pw, ph = w, (h - gap) // 2
                case "Junior Big (70/30)":
                    pw = int((w - gap) * 0.7) if i == 0 else (w - gap) - int((w - gap) * 0.7)
                    ph = h
                case "Senior Big (70/30)":
                    pw = int((w - gap) * 0.3) if i == 0 else (w - gap) - int((w - gap) * 0.3)
                    ph = h
                case "PIP - Senior Big (Junior Small)":
                    pw = int(w * 0.4) if i == 0 else w
                    ph = int(h * 0.4) if i == 0 else h
                case "PIP - Junior Big (Senior Small)":
                    pw = w if i == 0 else int(w * 0.4)
                    ph = h if i == 0 else int(h * 0.4)
                case _: pw, ph = (w - gap) // 2, h
            lang_text = self.lang_cb.currentText()
            language = self._detect_language(self._current_name, code) if lang_text == "Auto" else lang_text
            code_lines = code.count("\n") + 1
            kb_overlay = None
            kb_h = 0
            if show_kb:
                kb_overlay = KeyboardOverlay(pw, ph, kb_layout, theme, (ph - 2 * pad) // 3, kb_pos, kb_op)
                kb_h = kb_overlay.height_needed()
            current_font = j_font if i == 0 else s_font
            font_size = (CodeRenderer.auto_font_size(code_lines, pw, ph, pad, chrome, ln, 4, code, current_font, kb_h)
                         if self.font_size_auto.isChecked() else max(8, int(self.font_size_sp.value())))
            renderer = CodeRenderer(pw, ph, theme_name, current_font, font_size, ln, chrome, pad, 4, title,
                                    language, kb_overlay, self._bg_image_path if i == 0 else None,
                                    code_lines, self.cursor_glow_chk.isChecked(),
                                    self.watermark_chk.isChecked() and i == 0,
                                    theme.get(accent_key, "#7aa2f7"))
            animator = TypingAnimator(code, profile, seed=i * 1000 + 42)
            panes.append((renderer, animator))
        return MultiPaneRenderer(panes=panes, frame_w=w, frame_h=h, num_panes=2, pane_layout=pane_layout, gap=gap)

    def _get_multi_pane(self) -> Optional[MultiPaneRenderer]:
        key = (
            self.export_format_cb.currentText(), self.res_cb.currentText(),
            self.theme_cb.currentText(), self.j_font_cb.currentText(),
            self.s_font_cb.currentText(), self.font_size_auto.isChecked(),
            self.font_size_sp.value(), self.chrome_chk.isChecked(),
            self.line_nums_chk.isChecked(), self.cursor_glow_chk.isChecked(),
            self.watermark_chk.isChecked(), self._bg_image_path,
            self.kb_chk.isChecked(), self.kb_layout_cb.currentText(),
            self.kb_pos_cb.currentText(), self.kb_opacity.value(),
            self.j_wpm.value(), self.j_pause.value(), self.j_burst.value(),
            self.s_wpm.value(), self.s_pause.value(), self.s_burst.value(),
            self.start_pause_sp.value(), self.end_pause_sp.value(),
            self._current_junior_code, self._current_senior_code,
            self.lang_cb.currentText(), self.pane_layout_cb.currentText(),
            self.editor_padding_sp.value(), self.pane_gap_sp.value()
        )
        if key != self._cached_key:
            self._cached_key = key
            self._cached_mp = self._build_panes()
            self._preview_scratch = QImage(self._cached_mp.frame_w, self._cached_mp.frame_h, QImage.Format_RGB32)
        return self._cached_mp

    def _update_preview(self) -> None:
        try:
            mp = self._get_multi_pane()
            if mp is None or not mp.panes:
                return
            total_dur = mp.duration()
            t = total_dur * self._preview_progress
            state = mp.compute_state(t)
            qimg = mp.render_frame(t, self._preview_scratch, precomputed_state=state)
            scaled = QPixmap.fromImage(qimg).scaled(
                self.preview_label.size(),
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            )
            self.preview_label.setPixmap(scaled)
            cur_m, cur_s = divmod(int(t), 60)
            tot_m, tot_s = divmod(int(total_dur), 60)
            self.time_label.setText(f"{cur_m}:{cur_s:02d} / {tot_m}:{tot_s:02d}")
            self.pct_label.setText(f"{int(self._preview_progress * 100)}%")
            total_visible = sum(len(s[0]) for s in state)
            total_chars = sum(len(a.text_snapshots[-1]) for _, a in mp.panes)
            elapsed_min = max(t / 60.0, 0.001)
            wpm = int((total_visible / 5) / elapsed_min) if t > 0.3 else 0
            self.stats_label.setText(f"  |  WPM: {wpm}  |  Chars: {total_visible}/{total_chars}")
            self.info_label.setText(f"{mp.frame_w}×{mp.frame_h}  |  2 panes  |  Font: {mp.panes[0][0].font_family} {mp.panes[0][0].font_size}px  |  {total_visible}/{total_chars} chars")
            self.duration_label.setText(f"Duration: {_format_eta(total_dur)}")
            self.frame_slider.blockSignals(True)
            self.frame_slider.setValue(int(self._preview_progress * 1000))
            self.frame_slider.blockSignals(False)
        except Exception as e:
            log.debug("Preview update error: %s", e)

    def _on_slider(self, value: int) -> None:
        self._stop_preview_anim()
        self._preview_progress = value / 1000.0
        self._update_preview()

    def _seek_preview(self, delta: float) -> None:
        self._stop_preview_anim()
        mp = self._get_multi_pane()
        if mp is None: return
        total = mp.duration()
        self._preview_anim_t = max(0, min(total, total * self._preview_progress + delta))
        self._preview_progress = max(0, min(1.0, self._preview_anim_t / total)) if total > 0 else 0
        self._update_preview()

    def _seek_frame(self, direction: int) -> None:
        self._stop_preview_anim()
        mp = self._get_multi_pane()
        if mp is None: return
        fps = self.fps_sp.value()
        delta = direction / fps
        total = mp.duration()
        self._preview_anim_t = max(0, min(total, total * self._preview_progress + delta))
        self._preview_progress = self._preview_anim_t / total if total > 0 else 0
        self._update_preview()

    def _toggle_loop(self, checked: bool) -> None:
        self._preview_loop = checked

    def _toggle_fullscreen(self) -> None:
        if self.preview_label.isFullScreen():
            self.preview_label.showNormal()
            self.preview_label.setParent(self._preview_parent_container)
            self.preview_label.show()
        else:
            self._preview_parent_container = self.preview_label.parentWidget()
            self.preview_label.setParent(None)
            self.preview_label.showFullScreen()
            self._update_preview()

    def _on_preview_click(self, event) -> None:
        self._toggle_preview_anim()

    def _toggle_preview_anim(self) -> None:
        if self._preview_animating:
            self._stop_preview_anim()
        else:
            mp = self._get_multi_pane()
            if mp is None: return
            total = mp.duration()
            if self._preview_progress >= 0.999:
                self._preview_progress = 0.0
                self._preview_anim_t = 0.0
            else:
                self._preview_anim_t = total * self._preview_progress
            self._preview_animating = True
            self.play_btn.setText("⏸ Pause")
            self.play_pause_btn.setText("⏸ Pause")
            self._preview_clock.start()
            if self.sound_chk.isChecked():
                vol = self.vol_sp.value() / 100.0
                ts = mp.char_timestamps_all()
                total_dur = mp.duration()
                if total_dur <= 300.0 and ts:
                    def on_audio_ready(data):
                        if data and isinstance(data, bytes) and self._preview_animating:
                            self._play_audio_bytes(data, vol)
                    self._start_audio_worker(ts, vol, callback=on_audio_ready)
            bgm_path = self.bgm_edit.text().strip()
            if bgm_path and os.path.exists(bgm_path):
                self._bgm_player.setSource(QUrl.fromLocalFile(bgm_path))
                self._bgm_out.setVolume(self.bgm_vol_sp.value() / 100.0)
                self._bgm_player.play()
            self._preview_timer.start()

    def _advance_preview(self) -> None:
        dt = min(self._preview_clock.restart() / 1000.0, 0.1)
        self._preview_anim_t += dt
        mp = self._get_multi_pane()
        if mp is None:
            self._stop_preview_anim()
            return
        total = mp.duration()
        if self._preview_anim_t >= total:
            if self._preview_loop:
                self._preview_anim_t = 0.0
            else:
                self._preview_anim_t = total
                self._stop_preview_anim()
        self._preview_progress = min(1.0, self._preview_anim_t / total) if total > 0 else 0.0
        self._update_preview()

    def _stop_preview_anim(self) -> None:
        self._preview_animating = False
        self._preview_timer.stop()
        self.play_btn.setText("▶ Animate")
        self.play_pause_btn.setText("▶ Play")
        if self._audio_player:
            self._audio_player.stop()
            self._audio_player.setSource(QUrl())
        if self._bgm_player:
            self._bgm_player.stop()
            self._bgm_player.setSource(QUrl())

    def _reset_preview(self) -> None:
        self._stop_preview_anim()
        self._preview_progress = 0.0
        self._preview_anim_t = 0.0
        self._update_preview()

    def _save_settings(self) -> None:
        try:
            data = {
                "theme": self.theme_cb.currentText(),
                "j_font": self.j_font_cb.currentText(),
                "s_font": self.s_font_cb.currentText(),
                "font_size_auto": self.font_size_auto.isChecked(),
                "font_size": self.font_size_sp.value(),
                "show_chrome": self.chrome_chk.isChecked(),
                "show_line_numbers": self.line_nums_chk.isChecked(),
                "cursor_glow": self.cursor_glow_chk.isChecked(),
                "watermark": self.watermark_chk.isChecked(),
                "bg_image_path": self._bg_image_path,
                "export_format": self.export_format_cb.currentText(),
                "pane_layout": self.pane_layout_cb.currentText(),
                "resolution": self.res_cb.currentText(),
                "fps": self.fps_sp.value(),
                "encoder": self.encoder_cb.currentText(),
                "start_pause": self.start_pause_sp.value(),
                "end_pause": self.end_pause_sp.value(),
                "j_wpm": self.j_wpm.value(),
                "j_pause": self.j_pause.value(),
                "j_burst": self.j_burst.value(),
                "s_wpm": self.s_wpm.value(),
                "s_pause": self.s_pause.value(),
                "s_burst": self.s_burst.value(),
                "sound_enabled": self.sound_chk.isChecked(),
                "sound_preset": self.sound_preset_cb.currentText(),
                "binaural": self.binaural_chk.isChecked(),
                "reverb_amt": self.reverb_sp.value(),
                "volume": self.vol_sp.value(),
                "kb_overlay": self.kb_chk.isChecked(),
                "kb_layout": self.kb_layout_cb.currentText(),
                "kb_position": self.kb_pos_cb.currentText(),
                "kb_opacity": self.kb_opacity.value(),
                "language": self.lang_cb.currentText(),
                "editor_padding": self.editor_padding_sp.value(),
                "pane_gap": self.pane_gap_sp.value(),
                "bgm_path": self.bgm_edit.text(),
                "bgm_volume": self.bgm_vol_sp.value(),
                "bgm_duck": self.bgm_duck_sp.value(),
                "naming_template": self.naming_edit.text(),
                "gen_thumbnail": self.gen_thumb_chk.isChecked(),
                "gen_chapters": self.gen_chapters_chk.isChecked(),
                "recursive": self.recurse_chk.isChecked(),
                "depth": self.depth_sp.value(),
            }
            with open(str(SETTINGS_FILE), "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            log.warning("Failed to save settings: %s", e)

    def _load_settings(self) -> None:
        if not SETTINGS_FILE.is_file():
            return
        try:
            with open(str(SETTINGS_FILE), "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            return
        self._loading_settings = True
        try:
            def _set(cb, key):
                if key in data:
                    idx = cb.findText(data[key])
                    if idx >= 0:
                        cb.setCurrentIndex(idx)
            _set(self.theme_cb, "theme")
            _set(self.j_font_cb, "j_font")
            _set(self.s_font_cb, "s_font")
            if "font_size_auto" in data: self.font_size_auto.setChecked(bool(data["font_size_auto"]))
            if "font_size" in data: self.font_size_sp.setValue(int(data["font_size"]))
            if "show_chrome" in data: self.chrome_chk.setChecked(bool(data["show_chrome"]))
            if "show_line_numbers" in data: self.line_nums_chk.setChecked(bool(data["show_line_numbers"]))
            if "cursor_glow" in data: self.cursor_glow_chk.setChecked(bool(data["cursor_glow"]))
            if "watermark" in data: self.watermark_chk.setChecked(bool(data["watermark"]))
            if "bg_image_path" in data:
                self._bg_image_path = str(data["bg_image_path"])
                self.bg_edit.setText(self._bg_image_path)
            _set(self.export_format_cb, "export_format")
            self._populate_resolutions()
            _set(self.res_cb, "resolution")
            if "fps" in data: self.fps_sp.setValue(int(data["fps"]))
            _set(self.encoder_cb, "encoder")
            if "start_pause" in data: self.start_pause_sp.setValue(float(data["start_pause"]))
            if "end_pause" in data: self.end_pause_sp.setValue(float(data["end_pause"]))
            for pfx in ["j", "s"]:
                for k in ["wpm", "pause", "burst"]:
                    key = f"{pfx}_{k}"
                    if key in data:
                        getattr(self, key).setValue(float(data[key]) if k != "wpm" else int(data[key]))
            if "sound_enabled" in data: self.sound_chk.setChecked(bool(data["sound_enabled"]))
            _set(self.sound_preset_cb, "sound_preset")
            if "binaural" in data: self.binaural_chk.setChecked(bool(data["binaural"]))
            if "reverb_amt" in data: self.reverb_sp.setValue(float(data["reverb_amt"]))
            if "volume" in data: self.vol_sp.setValue(int(data["volume"]))
            if "kb_overlay" in data: self.kb_chk.setChecked(bool(data["kb_overlay"]))
            _set(self.kb_layout_cb, "kb_layout")
            _set(self.kb_pos_cb, "kb_position")
            if "kb_opacity" in data: self.kb_opacity.setValue(float(data["kb_opacity"]))
            _set(self.lang_cb, "language")
            _set(self.pane_layout_cb, "pane_layout")
            if "editor_padding" in data: self.editor_padding_sp.setValue(int(data["editor_padding"]))
            if "pane_gap" in data: self.pane_gap_sp.setValue(int(data["pane_gap"]))
            if "bgm_path" in data: self.bgm_edit.setText(str(data["bgm_path"]))
            if "bgm_volume" in data: self.bgm_vol_sp.setValue(int(data["bgm_volume"]))
            if "bgm_duck" in data: self.bgm_duck_sp.setValue(int(data["bgm_duck"]))
            if "naming_template" in data: self.naming_edit.setText(str(data["naming_template"]))
            if "gen_thumbnail" in data: self.gen_thumb_chk.setChecked(bool(data["gen_thumbnail"]))
            if "gen_chapters" in data: self.gen_chapters_chk.setChecked(bool(data["gen_chapters"]))
            if "recursive" in data: self.recurse_chk.setChecked(bool(data["recursive"]))
            if "depth" in data: self.depth_sp.setValue(int(data["depth"]))
        finally:
            self._loading_settings = False

    def closeEvent(self, event) -> None:
        self._save_settings()
        self._stop_preview_anim()
        if self._audio_tmp_file:
            self._safe_delete_file(self._audio_tmp_file)
            self._audio_tmp_file = None
        if self._audio_workers:
            for t in list(self._audio_workers):
                t.quit()
                t.wait(3000)
            self._audio_workers.clear()
        if self._exporter:
            self._exporter.cancel()
            self._exporter.wait(15000)
            self._exporter = None
        super().closeEvent(event)


# =====================================================================
# SECTION 15 — APPLICATION ENTRY POINT
# =====================================================================

STYLE = """
QMainWindow, QDialog { background: #1e1e2e; }
QGroupBox { color: #cdd6f4; font-weight: bold; font-size: 13px; border: 1px solid #45475a; border-radius: 8px; margin-top: 12px; padding-top: 16px; }
QGroupBox::title { subcontrol-origin: margin; left: 12px; }
QLabel { color: #cdd6f4; }
QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox { background: #313244; color: #cdd6f4; border: 1px solid #45475a; border-radius: 4px; padding: 4px 8px; min-height: 24px; }
QComboBox::drop-down { border: none; }
QComboBox QAbstractItemView { background: #313244; color: #cdd6f4; selection-background-color: #45475a; }
QCheckBox { color: #cdd6f4; spacing: 6px; }
QCheckBox::indicator { width: 18px; height: 18px; border-radius: 4px; border: 2px solid #45475a; background: #313244; }
QCheckBox::indicator:checked { background: #89b4fa; border-color: #89b4fa; }
QPushButton { background: #313244; color: #cdd6f4; border: 1px solid #45475a; border-radius: 6px; padding: 6px 16px; font-size: 13px; }
QPushButton:hover { background: #45475a; }
QProgressBar { background: #313244; border: none; border-radius: 4px; text-align: center; color: #cdd6f4; min-height: 20px; }
QProgressBar::chunk { background: #89b4fa; border-radius: 4px; }
QTabWidget::pane { border: 1px solid #45475a; border-radius: 6px; background: #1e1e2e; top: -1px; }
QTabBar::tab { background: #313244; color: #a6adc8; padding: 8px 18px; border: 1px solid #45475a; border-bottom: none; border-top-left-radius: 6px; border-top-right-radius: 6px; font-size: 12px; font-weight: bold; margin-right: 2px; }
QTabBar::tab:selected { background: #1e1e2e; color: #cdd6f4; border-bottom: 2px solid #89b4fa; }
QTabBar::tab:hover:!selected { background: #45475a; color: #cdd6f4; }
QStatusBar { color: #a6adc8; font-size: 12px; }
QTableWidget { background: #181825; color: #cdd6f4; gridline-color: #313244; border: none; outline: none; }
QTableWidget::item { padding: 4px 6px; border-bottom: 1px solid #11111b; }
QTableWidget::item:selected { background: #89b4fa; color: #1e1e2e; }
QHeaderView::section { background: #1e1e2e; color: #a6adc8; border: none; padding: 4px; font-size: 10px; }
QSlider::groove:horizontal { background: #313244; height: 4px; border-radius: 2px; }
QSlider::handle:horizontal { background: #89b4fa; width: 14px; height: 14px; margin: -5px 0; border-radius: 7px; }
QSlider::sub-page:horizontal { background: #89b4fa; border-radius: 2px; }
QPlainTextEdit { background: #11111b; color: #cdd6f4; border: 1px solid #45475a; border-radius: 4px; }
QToolTip { background: #313244; color: #cdd6f4; border: 1px solid #45475a; border-radius: 4px; padding: 4px 8px; }
"""


def main() -> int:
    """Initialize and run the application."""
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(STYLE)
    pal = QPalette()
    pal.setColor(QPalette.Window, QColor("#1e1e2e"))
    pal.setColor(QPalette.WindowText, QColor("#cdd6f4"))
    pal.setColor(QPalette.Base, QColor("#313244"))
    pal.setColor(QPalette.Text, QColor("#cdd6f4"))
    pal.setColor(QPalette.Button, QColor("#313244"))
    pal.setColor(QPalette.ButtonText, QColor("#cdd6f4"))
    pal.setColor(QPalette.Highlight, QColor("#89b4fa"))
    pal.setColor(QPalette.HighlightedText, QColor("#1e1e2e"))
    app.setPalette(pal)
    win = MainWindow()
    win.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())