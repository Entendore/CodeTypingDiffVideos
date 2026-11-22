#!/usr/bin/env python3
"""
Junior vs Senior Dev Code Typing Studio
=======================================
Optimized for YouTube (High-Fidelity ASMR Audio & Professional Video Encoding).
Requirements:
pip install PySide6 numpy
# Optional: pip install scipy numba  (for acceleration)
# FFmpeg must be on PATH for video export
"""
from __future__ import annotations
import bisect
import io
import json
import logging
import math
import os
import platform
import random
import re
import subprocess
import sys
import shutil
import tempfile
import threading
import time as _time
import wave
import faulthandler
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Callable
import numpy as np
from PySide6.QtCore import (
    QEvent, QPointF, QPoint, QRect, Qt, QThread, Signal, Slot, QTimer, QUrl,
    QBuffer, QIODevice, QObject, QSize, QModelIndex, QSettings,
    QStandardPaths, QPropertyAnimation, QEasingCurve, QRegularExpression,
    QElapsedTimer
)
from PySide6.QtGui import (
    QColor, QFont, QFontDatabase, QFontMetrics, QImage, QLinearGradient,
    QPainter, QPalette, QPen, QBrush, QPainterPath, QPixmap, QPolygonF,
    QTextCharFormat, QSyntaxHighlighter, QTextCursor, QTextFormat,
    QKeySequence, QShortcut,
    QStandardItemModel, QStandardItem,
)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtWidgets import (
    QApplication, QCheckBox, QComboBox, QDialog, QDoubleSpinBox,
    QFileDialog, QGridLayout, QGroupBox, QHBoxLayout, QHeaderView,
    QLabel, QMainWindow, QMessageBox, QProgressBar, QPushButton,
    QSizePolicy, QStatusBar, QStyleFactory, QTabWidget,
    QTableWidget, QTableWidgetItem, QVBoxLayout, QWidget, QScrollArea,
    QFormLayout, QFrame, QDialogButtonBox, QSlider, QGraphicsDropShadowEffect,
    QLineEdit, QSpinBox, QMenu, QSplitter, QPlainTextEdit, QListView,
    QRadioButton, QProgressDialog, QStyledItemDelegate, QStyle,
)

# Enable faulthandler to print tracebacks on hard segfaults
faulthandler.enable()

# =====================================================================
# 1. LOGGING & CONSTANTS
# =====================================================================
log = logging.getLogger("JuniorSeniorStudio")
log.setLevel(logging.INFO)
_fh = logging.FileHandler("studio.log", mode='w', encoding='utf-8')
_fh.setFormatter(logging.Formatter("%(asctime)s | %(levelname)-7s | %(message)s", datefmt="%H:%M:%S"))
log.addHandler(_fh)
log.addHandler(logging.StreamHandler())

CWD = os.getcwd()
INPUT_DIR  = os.path.join(CWD, "input")
OUTPUT_DIR = os.path.join(CWD, "output")
TEMP_DIR   = os.path.join(CWD, "temp")
SETTINGS_FILE = os.path.join(CWD, "settings.json")

for _d in (INPUT_DIR, OUTPUT_DIR, TEMP_DIR):
    os.makedirs(_d, exist_ok=True)

SUPPORTED_EXTENSIONS = frozenset({
    ".py", ".js", ".ts", ".jsx", ".tsx", ".java", ".c", ".cpp", ".h",
    ".hpp", ".cs", ".go", ".rs", ".rb", ".php", ".swift", ".kt",
    ".sh", ".bash", ".zsh", ".sql", ".html", ".css", ".scss", ".json",
    ".yaml", ".yml", ".toml", ".ini", ".cfg", ".txt", ".md",
    ".lua", ".dart", ".r", ".m",
})

EXT_TO_LANGUAGE: dict[str, str] = {
    ".py": "Python", ".js": "JavaScript", ".jsx": "JavaScript",
    ".ts": "TypeScript", ".tsx": "TypeScript",
    ".java": "CFamily", ".c": "CFamily", ".cpp": "CFamily",
    ".h": "CFamily", ".hpp": "CFamily", ".cs": "CFamily",
    ".go": "Go", ".rs": "Rust", ".rb": "Python", ".php": "Python",
    ".swift": "CFamily", ".kt": "CFamily", ".sh": "Python",
    ".lua": "Python", ".dart": "CFamily",
}

# =====================================================================
# 2. THEMES
# =====================================================================
THEMES: Dict[str, Dict[str, str]] = {
    "Tokyo Night": {
        "background": "#16171e", "foreground": "#c0caf5",
        "comment": "#565f89", "keyword": "#bb9af7", "string": "#9ece6a",
        "number": "#ff9e64", "function": "#7aa2f7", "builtin": "#7aa2f7",
        "decorator": "#e0af68", "operator": "#89ddff", "class_name": "#7dcfff",
        "line_number": "#3b4261", "current_line": "#1a1b26", "cursor": "#c0caf5",
        "title_bar": "#1a1b26", "title_text": "#7aa2f7",
        "window_border": "#16171e",
        "junior_accent": "#7aa2f7", "senior_accent": "#9ece6a",
    },
    "Dracula": {
        "background": "#282a36", "foreground": "#f8f8f2",
        "comment": "#6272a4", "keyword": "#ff79c6", "string": "#f1fa8c",
        "number": "#bd93f9", "function": "#50fa7b", "builtin": "#8be9fd",
        "decorator": "#50fa7b", "operator": "#ff79c6", "class_name": "#8be9fd",
        "line_number": "#6272a4", "current_line": "#44475a", "cursor": "#f8f8f2",
        "title_bar": "#21222c", "title_text": "#8be9fd",
        "window_border": "#191a21",
        "junior_accent": "#8be9fd", "senior_accent": "#50fa7b",
    },
    "Monokai": {
        "background": "#272822", "foreground": "#f8f8f2",
        "comment": "#75715e", "keyword": "#f92672", "string": "#e6db74",
        "number": "#ae81ff", "function": "#a6e22e", "builtin": "#66d9ef",
        "decorator": "#a6e22e", "operator": "#f92672", "class_name": "#66d9ef",
        "line_number": "#75715e", "current_line": "#3e3d32", "cursor": "#f8f8f2",
        "title_bar": "#1e1f1c", "title_text": "#a6e22e",
        "window_border": "#1e1f1c",
        "junior_accent": "#66d9ef", "senior_accent": "#a6e22e",
    },
    "One Dark": {
        "background": "#282c34", "foreground": "#abb2bf",
        "comment": "#5c6370", "keyword": "#c678dd", "string": "#98c379",
        "number": "#d19a66", "function": "#61afef", "builtin": "#e5c07b",
        "decorator": "#56b6c2", "operator": "#c678dd", "class_name": "#e5c07b",
        "line_number": "#4b5263", "current_line": "#2c313c", "cursor": "#528bff",
        "title_bar": "#21252b", "title_text": "#61afef",
        "window_border": "#181a1f",
        "junior_accent": "#61afef", "senior_accent": "#98c379",
    },
    "GitHub Dark": {
        "background": "#0d1117", "foreground": "#c9d1d9",
        "comment": "#8b949e", "keyword": "#ff7b72", "string": "#a5d6ff",
        "number": "#79c0ff", "function": "#d2a8ff", "builtin": "#ffa657",
        "decorator": "#ffa657", "operator": "#ff7b72", "class_name": "#ffa657",
        "line_number": "#484f58", "current_line": "#161b22", "cursor": "#58a6ff",
        "title_bar": "#010409", "title_text": "#58a6ff",
        "window_border": "#010409",
        "junior_accent": "#58a6ff", "senior_accent": "#7ee787",
    },
    "Nord": {
        "background": "#2e3440", "foreground": "#d8dee9",
        "comment": "#616e88", "keyword": "#81a1c1", "string": "#a3be8c",
        "number": "#b48ead", "function": "#88c0d0", "builtin": "#81a1c1",
        "decorator": "#ebcb8b", "operator": "#81a1c1", "class_name": "#8fbcbb",
        "line_number": "#4c566a", "current_line": "#3b4252", "cursor": "#d8dee9",
        "title_bar": "#3b4252", "title_text": "#88c0d0",
        "window_border": "#2e3440",
        "junior_accent": "#88c0d0", "senior_accent": "#a3be8c",
    },
    "Gruvbox": {
        "background": "#282828", "foreground": "#ebdbb2",
        "comment": "#928374", "keyword": "#fb4934", "string": "#b8bb26",
        "number": "#d3869b", "function": "#fabd2f", "builtin": "#fe8019",
        "decorator": "#fe8019", "operator": "#fb4934", "class_name": "#fabd2f",
        "line_number": "#7c6f64", "current_line": "#3c3836", "cursor": "#ebdbb2",
        "title_bar": "#3c3836", "title_text": "#fabd2f",
        "window_border": "#282828",
        "junior_accent": "#fabd2f", "senior_accent": "#b8bb26",
    },
    "Solarized Dark": {
        "background": "#002b36", "foreground": "#839496",
        "comment": "#586e75", "keyword": "#859900", "string": "#2aa198",
        "number": "#d33682", "function": "#268bd2", "builtin": "#b58900",
        "decorator": "#cb4b16", "operator": "#859900", "class_name": "#b58900",
        "line_number": "#073642", "current_line": "#073642", "cursor": "#839496",
        "title_bar": "#073642", "title_text": "#268bd2",
        "window_border": "#002b36",
        "junior_accent": "#268bd2", "senior_accent": "#859900",
    },
    "Catppuccin": {
        "background": "#24273a", "foreground": "#cad3f5",
        "comment": "#6e738d", "keyword": "#c6a0f6", "string": "#a6da95",
        "number": "#f5a97f", "function": "#8aadf4", "builtin": "#8bd5ca",
        "decorator": "#f5a97f", "operator": "#91d7e3", "class_name": "#8bd5ca",
        "line_number": "#494d64", "current_line": "#363a4f", "cursor": "#cad3f5",
        "title_bar": "#363a4f", "title_text": "#8aadf4",
        "window_border": "#24273a",
        "junior_accent": "#8aadf4", "senior_accent": "#a6da95",
    },
}

EXPORT_FORMATS: Dict[str, dict] = {
    "YouTube (16:9)": {
        "resolutions": OrderedDict([
            ("1920x1080", (1920, 1080)),
            ("1280x720",  (1280, 720)),
            ("3840x2160", (3840, 2160)),
        ]),
        "orientation": "landscape",
    },
    "YouTube Shorts (9:16)": {
        "resolutions": OrderedDict([
            ("1080x1920", (1080, 1920)),
            ("720x1280",  (720, 1280)),
        ]),
        "orientation": "portrait",
    },
}

ENCODERS = {
    "YouTube Pro (H.264/AAC)": {
        "base": ["-c:v", "libx264", "-preset", "slow", "-crf", "17", "-profile:v", "high", "-pix_fmt", "yuv420p"],
        "use_dynamic_vbv": True,
        "use_dynamic_gop": True,
        "color_tags": True
    },
    "x264 (CPU, Best Quality)": {
        "base": ["-c:v", "libx264", "-preset", "slow", "-crf", "16", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True,
        "color_tags": True
    },
    "x264 (CPU, Fast)": {
        "base": ["-c:v", "libx264", "-preset", "medium", "-crf", "20", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True,
        "color_tags": True
    },
    "NVENC (NVIDIA)": {
        "base": ["-c:v", "h264_nvenc", "-preset", "p5", "-rc", "vbr", "-cq", "19", "-b:v", "0", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True,
        "color_tags": True
    },
    "QSV (Intel)": {
        "base": ["-c:v", "h264_qsv", "-preset", "medium", "-global_quality", "19", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True,
        "color_tags": True
    },
    "AMF (AMD)": {
        "base": ["-c:v", "h264_amf", "-preset", "speed", "-rc", "cqp", "-qp_i", "19", "-qp_p", "19", "-pix_fmt", "yuv420p"],
        "use_dynamic_gop": True,
        "color_tags": True
    },
}

QUALITY_PRESETS = {
    "Draft (720p, 30fps)": {"res": "1280x720", "fps": 30, "encoder": "x264 (CPU, Fast)"},
    "Medium (1080p, 30fps)": {"res": "1920x1080", "fps": 30, "encoder": "YouTube Pro (H.264/AAC)"},
    "High (1080p, 60fps)": {"res": "1920x1080", "fps": 60, "encoder": "YouTube Pro (H.264/AAC)"},
    "Ultra (4K, 60fps)": {"res": "3840x2160", "fps": 60, "encoder": "YouTube Pro (H.264/AAC)"},
}

# =====================================================================
# 3. LANGUAGE DEFINITIONS & TOKENIZER
# =====================================================================
_LANG_DATA: Dict[str, dict] = {
    "Python": {
        "keywords": {
            "False","None","True","and","as","assert","async","await","break",
            "class","continue","def","del","elif","else","except","finally",
            "for","from","global","if","import","in","is","lambda","nonlocal",
            "not","or","pass","raise","return","try","while","with","yield",
        },
        "builtins": {
            "print","len","range","int","str","float","list","dict","set","tuple",
            "bool","type","isinstance","enumerate","zip","map","filter","sorted",
            "reversed","open","super","property","staticmethod","classmethod",
            "abs","max","min","sum","any","all","hash","id","input","format",
            "hex","oct","bin","round","pow","divmod","chr","ord","repr","vars",
            "dir","getattr","setattr","hasattr","delattr","callable","iter","next",
        },
        "extra_patterns": [("decorator", r"@\w+(\.\w+)*")],
        "comment": r"#[^\n]*",
        "string":  r'"""[\s\S]*?"""|\'\'\'[\s\S]*?\'\'\'|"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'',
        "number":  r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b",
    },
    "JavaScript": {
        "keywords": {
            "break","case","catch","class","const","continue","debugger","default",
            "delete","do","else","export","extends","finally","for","function","if",
            "import","in","instanceof","let","new","of","return","static","super",
            "switch","this","throw","try","typeof","var","void","while","with",
            "yield","async","await","from","as","true","false","null","undefined",
        },
        "builtins": {
            "console","Math","JSON","Array","Object","String","Number","Boolean",
            "Date","RegExp","Error","Map","Set","Promise","Symbol","Proxy",
            "Reflect","parseInt","parseFloat","isNaN","isFinite","encodeURI",
            "decodeURI","setTimeout","setInterval","clearTimeout","clearInterval",
            "fetch","document","window","require","module","process","Buffer",
        },
        "extra_patterns": [],
        "comment": r"//[^\n]*|/\*[\s\S]*?\*/",
        "string":  r'`(?:[^`\\]|\\.)*`|"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'',
        "number":  r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b",
    },
    "TypeScript": "JavaScript",
    "CFamily": {
        "keywords": {
            "auto","break","case","char","const","continue","default","do",
            "double","else","enum","extern","float","for","goto","if","inline",
            "int","long","register","return","short","signed","sizeof","static",
            "struct","switch","typedef","union","unsigned","void","volatile",
            "while","class","namespace","template","typename","public","private",
            "protected","virtual","override","final","new","delete","try","catch",
            "throw","using","true","false","nullptr","boolean","byte","extends",
            "implements","import","instanceof","interface","native","package",
            "super","synchronized","this","throws","transient","abstract","assert",
        },
        "builtins": {
            "printf","scanf","malloc","free","sizeof","strlen","std","cout",
            "cin","endl","string","vector","map","set","println","System","Math",
        },
        "extra_patterns": [],
        "comment": r"//[^\n]*|/\*[\s\S]*?\*/",
        "string":  r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'',
        "number":  r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b",
    },
    "Go": {
        "keywords": {
            "break","case","chan","const","continue","default","defer","else",
            "fallthrough","for","func","go","goto","if","import","interface",
            "map","package","range","return","select","struct","switch","type",
            "var","nil","true","false","iota",
        },
        "builtins": {
            "fmt","os","io","strings","strconv","math","time","len","cap",
            "make","new","append","copy","delete","panic","recover","print","println",
        },
        "extra_patterns": [],
        "comment": r"//[^\n]*|/\*[\s\S]*?\*/",
        "string":  r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'|`[^`]*`',
        "number":  r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b",
    },
    "Rust": {
        "keywords": {
            "fn","let","mut","const","static","if","else","for","while","loop",
            "match","return","break","continue","in","as","use","mod","pub",
            "struct","enum","trait","impl","where","self","Self","super","crate",
            "extern","ref","move","async","await","dyn","unsafe","true","false",
        },
        "builtins": {
            "println","print","format","vec","String","Vec","Option","Result",
            "Box","Rc","Arc","Some","None","Ok","Err","HashMap","BTreeMap","HashSet",
        },
        "extra_patterns": [],
        "comment": r"//[^\n]*|/\*[\s\S]*?\*/",
        "string":  r'"[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'',
        "number":  r"\b\d+\.?\d*(?:e[+-]?\d+)?\b|0x[0-9a-fA-F]+\b",
    },
}

for _k, _v in list(_LANG_DATA.items()):
    if isinstance(_v, str) and _v in _LANG_DATA:
        _LANG_DATA[_k] = _LANG_DATA[_v]

class Tokenizer:
    _COMPILED: Dict[str, re.Pattern] = {}
    _LOCK = threading.Lock()

    @classmethod
    def _compile(cls, lang: str) -> re.Pattern:
        if lang not in cls._COMPILED:
            with cls._LOCK:
                if lang not in cls._COMPILED:
                    data = _LANG_DATA.get(lang, _LANG_DATA["Python"])
                    patterns = list(data.get("extra_patterns", []))
                    patterns.extend([
                        ("comment",    data["comment"]),
                        ("string",     data["string"]),
                        ("number",     data["number"]),
                        ("keyword",    r"\b(?:" + "|".join(data["keywords"]) + r")\b"),
                        ("builtin",    r"\b(?:" + "|".join(data["builtins"]) + r")\b"),
                        ("function",   r"\b([a-zA-Z_]\w*)\s*(?=\()"),
                        ("identifier", r"\b[a-zA-Z_]\w*\b"),
                        ("operator",   r"[+\-*/%=<>!&|^~]+"),
                        ("bracket",    r"[(){}\[\]]"),
                        ("punctuation",r"[;:,.]"),
                        ("whitespace", r"\s+"),
                        ("other",      r"."),
                    ])
                    pat_str = "|".join(f"(?P<{n}>{p})" for n, p in patterns)
                    cls._COMPILED[lang] = re.compile(pat_str, re.MULTILINE | re.DOTALL)
        return cls._COMPILED[lang]

    @classmethod
    def tokenize(cls, text: str, lang: str) -> List[Tuple[str, str]]:
        compiled = cls._COMPILED.get(lang) or cls._compile(lang)
        return [(m.lastgroup, m.group()) for m in compiled.finditer(text)]

# =====================================================================
# 4. DSP ENGINE
# =====================================================================
try:
    from scipy.signal import lfilter as _scipy_lfilter
    from scipy.signal import fftconvolve as _scipy_fftconvolve
    _HAS_SCIPY = True
except ImportError:
    _HAS_SCIPY = False

try:
    import numba
    _HAS_NUMBA = True
except ImportError:
    _HAS_NUMBA = False

class DSP:
    @staticmethod
    def env_exp(n, sr, attack=0.001, decay_rate=30.0, attack_curve=2.0):
        t = np.arange(n, dtype=np.float64) / sr
        env = np.exp(-t * decay_rate)
        a_samp = max(1, int(attack * sr))
        if a_samp < n:
            a_env = np.linspace(0, 1, a_samp) ** attack_curve
            env[:a_samp] = a_env * np.exp(-np.arange(a_samp, dtype=np.float64) / sr * decay_rate)
        return env

    @staticmethod
    def env_dahdsr(n, sr, delay=0.0, attack=0.001, hold=0.0, decay=0.05,
                   sustain=0.0, release=0.05, attack_curve=1.0,
                   decay_curve=1.0, release_curve=1.0):
        env = np.zeros(n, dtype=np.float64)
        i = 0
        ds = min(int(delay * sr), n - i); i += ds
        a_samp = min(int(attack * sr), n - i)
        if a_samp > 0:
            t_a = np.linspace(0, 1, a_samp)
            if attack_curve >= 1.0:
                env[i:i+a_samp] = t_a ** attack_curve
            else:
                env[i:i+a_samp] = 1 - (1 - t_a) ** (1.0 / max(0.001, attack_curve))
            i += a_samp
        h_samp = min(int(hold * sr), n - i)
        env[i:i+h_samp] = 1.0; i += h_samp
        d_samp = min(int(decay * sr), n - i)
        if d_samp > 0:
            t_d = np.linspace(0, 1, d_samp)
            env[i:i+d_samp] = (1 - sustain) * (1 - t_d) ** decay_curve + sustain
            i += d_samp
        r_samp = int(release * sr)
        s_end = max(i, n - r_samp)
        if s_end > i:
            env[i:s_end] = sustain; i = s_end
        r_samp = n - i
        if r_samp > 0:
            t_r = np.linspace(0, 1, r_samp)
            sv = env[i-1] if i > 0 else sustain
            env[i:i+r_samp] = sv * (1 - t_r) ** release_curve
        return env

    @staticmethod
    def fir_lowpass(cutoff, sr=44100, n_taps=127, window="blackman"):
        if n_taps % 2 == 0: n_taps += 1
        fc = cutoff / sr
        n = np.arange(n_taps, dtype=np.float64)
        center = (n_taps - 1) / 2.0
        h = np.sinc(2 * fc * (n - center))
        if window == "blackman":
            w = (0.42 - 0.5*np.cos(2*np.pi*n/(n_taps-1)) + 0.08*np.cos(4*np.pi*n/(n_taps-1)))
        elif window == "hamming":
            w = 0.54 - 0.46*np.cos(2*np.pi*n/(n_taps-1))
        elif window == "hann":
            w = 0.5 - 0.5*np.cos(2*np.pi*n/(n_taps-1))
        else:
            w = np.ones(n_taps)
        h *= w
        s = np.sum(h)
        if s > 0: h /= s
        return h

    @staticmethod
    def fir_highpass(cutoff, sr=44100, n_taps=127, window="blackman"):
        hlp = DSP.fir_lowpass(cutoff, sr, n_taps, window)
        h = -hlp; h[len(h)//2] += 1.0
        return h

    @staticmethod
    def fir_bandpass(low, high, sr=44100, n_taps=255, window="blackman"):
        return DSP.fir_lowpass(high, sr, n_taps, window) - DSP.fir_lowpass(low, sr, n_taps, window)

    @staticmethod
    def convolve(x, h):
        n = len(x); nh = len(h)
        if nh <= 1:
            return x * h[0] if nh == 1 else x
        if _HAS_SCIPY and nh > 64:
            return _scipy_fftconvolve(x, h, mode='full')[:n]
        if nh < 64 and n < 2048:
            return np.convolve(x, h, mode='full')[:n]
        n_fft = 1 << ((n + nh - 1).bit_length())
        X = np.fft.rfft(x, n_fft)
        H = np.fft.rfft(h, n_fft)
        return np.fft.irfft(X * H, n_fft)[:n]

    @staticmethod
    def filt_lp(x, cutoff, sr=44100, n_taps=127):
        return DSP.convolve(x, DSP.fir_lowpass(cutoff, sr, n_taps))

    @staticmethod
    def filt_hp(x, cutoff, sr=44100, n_taps=127):
        return DSP.convolve(x, DSP.fir_highpass(cutoff, sr, n_taps))

    @staticmethod
    def filt_bp(x, low, high, sr=44100, n_taps=255):
        return DSP.convolve(x, DSP.fir_bandpass(low, high, sr, n_taps))

    @staticmethod
    def filt_resonator(x, freq, q, sr=44100, gain=1.0):
        w0 = 2 * np.pi * freq / sr
        r = np.exp(-w0 / (2 * max(0.5, q)))
        wd = w0 * np.sqrt(max(0.0, 1.0 - 1.0/(4*q*q))) if q > 0.5 else w0
        decay_time = max(0.005, 6.0 * q / max(1.0, freq))
        n_ir = min(len(x), max(16, int(sr * decay_time)))
        t = np.arange(n_ir, dtype=np.float64)
        ir = (r ** t) * np.sin(wd * t)
        peak = np.max(np.abs(ir))
        if peak > 1e-10: ir = ir / peak * gain
        return DSP.convolve(x, ir)

    @staticmethod
    def sat_oversampled(x, drive=1.5):
        if drive <= 0: return x
        n = len(x)
        if n < 2: return np.tanh(x * drive) / max(0.001, np.tanh(drive))
        x_up = np.zeros(n * 2, dtype=np.float64)
        x_up[0::2] = x
        x_up[1:-1:2] = (x[:-1] + x[1:]) / 2.0
        x_up[-1] = x[-1]
        y_up = np.tanh(x_up * drive) / max(0.001, np.tanh(drive))
        y_down = (y_up[0:-1:2] + y_up[1::2]) / 2.0
        if len(y_down) < n: y_down = np.append(y_down, y_up[-1])
        elif len(y_down) > n: y_down = y_down[:n]
        return y_down

    @staticmethod
    def compressor_rms(x, sr, threshold_db=-12.0, ratio=3.0, attack_ms=10, release_ms=100):
        if threshold_db >= 0 or ratio <= 1: return x
        target_lin = 10**(threshold_db/20)
        env = np.abs(x).astype(np.float64)
        attack_coeff = np.exp(-1.0 / (sr * (attack_ms / 1000.0)))
        release_coeff = np.exp(-1.0 / (sr * (release_ms / 1000.0)))
        if _HAS_NUMBA:
            smooth_env = _nb_env_follower(env, attack_coeff, release_coeff)
            return _nb_apply_gain(x.astype(np.float64), smooth_env, target_lin, ratio)
        if _HAS_SCIPY:
            env_a = _scipy_lfilter([1-attack_coeff], [1, -attack_coeff], env)
            env_r = _scipy_lfilter([1-release_coeff], [1, -release_coeff], env)
            smooth_env = np.maximum(env_a, env_r)
        else:
            smooth_env = env
        gain = np.ones_like(x)
        mask = smooth_env > target_lin
        gain[mask] = 1.0 - (1.0 - 1.0/ratio) * (1.0 - target_lin / smooth_env[mask])
        return x * gain

    @staticmethod
    def lookahead_limiter(x, sr=44100, threshold_db=-1.0, release_ms=50):
        target_lin = 10**(threshold_db/20)
        peak = np.max(np.abs(x))
        if peak <= target_lin: return x
        attack_coeff = np.exp(-1.0 / (sr * 0.001))
        release_coeff = np.exp(-1.0 / (sr * (release_ms / 1000.0)))
        env = np.abs(x).astype(np.float64)
        if _HAS_NUMBA:
            smooth_env = _nb_env_follower(env, attack_coeff, release_coeff)
            gain = _nb_lookahead_gain(smooth_env, target_lin)
        else:
            gain = np.ones_like(x)
            mask = env > target_lin
            gain[mask] = target_lin / env[mask]
        lookahead = int(sr * 0.002)
        if lookahead > 0 and len(gain) > lookahead:
            gain = np.roll(gain, lookahead)
            gain[:lookahead] = gain[lookahead]
        return x * gain

    @staticmethod
    def dc_block(x, sr=44100):
        return DSP.filt_hp(x, 20.0, sr, n_taps=63)

    @staticmethod
    def osc_sine(freq, n, sr, phase=0.0):
        t = np.arange(n, dtype=np.float64) / sr
        return np.sin(2*np.pi*freq*t + phase)

    @staticmethod
    def osc_sweep(f_start, f_end, n, sr):
        if f_start <= 0: f_start = 1.0
        if f_end <= 0: f_end = 1.0
        t = np.arange(n, dtype=np.float64) / sr
        freq = f_start * (f_end / f_start) ** (t / (n/sr))
        phase = 2 * np.pi * np.cumsum(freq) / sr
        return np.sin(phase)

    @staticmethod
    def osc_fm(carrier, mod_ratio, mod_index, n, sr, phase=0.0):
        t = np.arange(n, dtype=np.float64) / sr
        return np.sin(2*np.pi*carrier*t + mod_index*np.sin(2*np.pi*carrier*mod_ratio*t) + phase)

    @staticmethod
    def osc_fm_multi(carrier, mod_ratios, mod_indices, n, sr):
        t = np.arange(n, dtype=np.float64) / sr
        ph = 2*np.pi*carrier*t
        for mr, mi in zip(mod_ratios, mod_indices):
            ph += mi * np.sin(2*np.pi*carrier*mr*t)
        return np.sin(ph)

    @staticmethod
    def osc_saw(freq, n, sr):
        t = np.arange(n, dtype=np.float64) / sr
        sig = np.zeros(n)
        for h in range(1, 17):
            fh = freq * h
            if fh >= sr * 0.45: break
            sig += np.sin(2*np.pi*fh*t) / h
        return sig * 0.5

    @staticmethod
    def noise_white(n, rng):
        return rng.randn(n).astype(np.float64)

    @staticmethod
    def noise_pink(n, rng):
        block_size = min(n, 44100 * 5)
        white = rng.randn(block_size).astype(np.float64)
        fft = np.fft.rfft(white)
        freqs = np.fft.rfftfreq(block_size, 1.0/44100)
        if len(freqs) > 1:
            freqs[0] = max(freqs[1], 1.0)
            fft[1:] /= np.sqrt(np.abs(freqs[1:]))
            fft[0] = 0
        pink_block = np.fft.irfft(fft, n=block_size)
        reps = n // block_size
        rem = n % block_size
        out = np.tile(pink_block, reps) if reps > 0 else np.array([], dtype=np.float64)
        if rem > 0:
            out = np.concatenate([out, pink_block[:rem]])
        return out

    @staticmethod
    def noise_brown(n, rng):
        white = rng.randn(n).astype(np.float64)
        brown = np.cumsum(white)
        brown -= np.mean(brown)
        peak = np.max(np.abs(brown))
        if peak > 0: brown = brown / peak
        return brown * 0.5

    @staticmethod
    def modal(modes, n, sr, inharmonicity=0.0):
        t = np.arange(n, dtype=np.float64) / sr
        out = np.zeros(n, dtype=np.float64)
        f0 = modes[0][0] if modes else 440.0
        for freq, decay, amp in modes:
            af = freq
            if inharmonicity > 0:
                nh = freq / f0
                af = freq * np.sqrt(1 + inharmonicity * nh * nh)
            out += np.sin(2*np.pi*af*t) * np.exp(-decay*t) * amp
        return out

    @staticmethod
    def sat_tanh(x, drive=1.0):
        if drive <= 0: return x
        return np.tanh(x * drive) / max(0.001, np.tanh(drive))

    @staticmethod
    def sat_hard(x, threshold=1.0):
        return np.clip(x, -threshold, threshold)

    @staticmethod
    def normalize(x, target_db=-1.0):
        peak = np.max(np.abs(x))
        if peak < 1e-10: return x
        return x * (10**(target_db/20) / peak)

    @staticmethod
    def to_int16(x, target_db=-1.0):
        x = DSP.normalize(x, target_db)
        x = DSP.sat_hard(x, 1.0)
        return (x * 32767).astype(np.int16)

    @staticmethod
    def master_mono(x, sr=44100, target_db=-0.1):
        if len(x) == 0: return x
        x = DSP.dc_block(x, sr)
        x = DSP.filt_hp(x, 25.0, sr, n_taps=127)
        low = DSP.filt_lp(x, 150, sr, n_taps=127)
        x = x + low * 0.15
        mid = DSP.filt_bp(x, 250, 500, sr, n_taps=255)
        x = x - mid * 0.15
        high = DSP.filt_hp(x, 6000, sr, n_taps=63)
        x = x + high * 0.25
        x = DSP.compressor_rms(x, sr, threshold_db=-15.0, ratio=2.5, attack_ms=10, release_ms=100)
        x = DSP.sat_oversampled(x, drive=1.4)
        x = DSP.lookahead_limiter(x, sr, threshold_db=target_db)
        return np.clip(x, -1.0, 1.0)

    @staticmethod
    def master_stereo(mix_l, mix_r, sr=44100, target_db=-0.1):
        if len(mix_l) == 0: return mix_l, mix_r
        mix_l = DSP.dc_block(mix_l, sr); mix_r = DSP.dc_block(mix_r, sr)
        mix_l = DSP.filt_hp(mix_l, 25.0, sr, n_taps=127); mix_r = DSP.filt_hp(mix_r, 25.0, sr, n_taps=127)
        mid = (mix_l + mix_r) * 0.5
        side = (mix_l - mix_r) * 0.5
        mid_low = DSP.filt_lp(mid, 150, sr, n_taps=127)
        mid += mid_low * 0.15
        mid_mid = DSP.filt_bp(mid, 250, 500, sr, n_taps=255)
        mid -= mid_mid * 0.15
        mid_high = DSP.filt_hp(mid, 6000, sr, n_taps=63)
        mid += mid_high * 0.25
        side = DSP.filt_hp(side, 200.0, sr, n_taps=127)
        side_high = DSP.filt_hp(side, 8000, sr, n_taps=63)
        side += side_high * 0.15
        mid = DSP.compressor_rms(mid, sr, threshold_db=-15.0, ratio=2.5, attack_ms=10, release_ms=100)
        side *= 1.1
        mix_l = mid + side
        mix_r = mid - side
        mix_l = DSP.sat_oversampled(mix_l, drive=1.4)
        mix_r = DSP.sat_oversampled(mix_r, drive=1.4)
        mix_l = DSP.lookahead_limiter(mix_l, sr, threshold_db=target_db)
        mix_r = DSP.lookahead_limiter(mix_r, sr, threshold_db=target_db)
        return np.clip(mix_l, -1.0, 1.0), np.clip(mix_r, -1.0, 1.0)

# =====================================================================
# 5. SOUND VOICES & PRESETS
# =====================================================================
@dataclass
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

class SoundRenderer:
    def __init__(self, sr=44100):
        self.sr = sr

    def render(self, voices, duration, rng):
        n = int(self.sr * duration)
        if n <= 0: return np.zeros(0, dtype=np.float64)
        mix = np.zeros(n, dtype=np.float64)
        for v in voices:
            sig = self._render_voice(v, n, rng)
            d_samp = int(v.delay * self.sr)
            if d_samp > 0:
                if d_samp >= n: continue
                sig = np.concatenate([np.zeros(d_samp, dtype=np.float64), sig[:n-d_samp]])
            if len(sig) < n:
                sig = np.concatenate([sig, np.zeros(n - len(sig))])
            else:
                sig = sig[:n]
            mix += sig
        return DSP.dc_block(mix, self.sr)

    def _render_voice(self, v, n, rng):
        if v.osc == "sine":
            sig = DSP.osc_sine(v.freq, n, self.sr)
        elif v.osc == "sweep":
            sig = DSP.osc_sweep(v.freq, v.freq_end, n, self.sr)
        elif v.osc == "fm":
            if v.fm_ratios:
                sig = DSP.osc_fm_multi(v.freq, v.fm_ratios, v.fm_indices, n, self.sr)
            else:
                sig = DSP.osc_fm(v.freq, v.fm_ratio, v.fm_index, n, self.sr)
        elif v.osc == "noise_white":
            sig = DSP.noise_white(n, rng)
        elif v.osc == "noise_pink":
            sig = DSP.noise_pink(n, rng)
        elif v.osc == "noise_brown":
            sig = DSP.noise_brown(n, rng)
        elif v.osc == "modal":
            sig = DSP.modal(v.modes, n, self.sr, v.inharmonicity) if v.modes else DSP.noise_white(n, rng)
        elif v.osc == "saw":
            sig = DSP.osc_saw(v.freq, n, self.sr)
        else:
            sig = np.zeros(n, dtype=np.float64)
        
        env = DSP.env_exp(n, self.sr, attack=v.attack, decay_rate=v.decay_rate, attack_curve=v.attack_curve)
        sig *= env
        if v.filt == "lp": sig = DSP.filt_lp(sig, v.f_cutoff, self.sr)
        elif v.filt == "hp": sig = DSP.filt_hp(sig, v.f_cutoff, self.sr)
        elif v.filt == "bp": sig = DSP.filt_bp(sig, v.f_cutoff, v.f_high, self.sr)
        elif v.filt == "resonator": sig = DSP.filt_resonator(sig, v.f_cutoff, v.f_q, self.sr)
        if v.drive > 0: sig = DSP.sat_tanh(sig, v.drive)
        sig *= v.gain
        return sig

def _v_click(freq, gain=0.5, delay=0.0, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.12, 0.12))
    return Voice(osc="sweep", freq=freq*1.8, freq_end=freq*0.9,
                 attack=0.0001, decay_rate=350.0, attack_curve=3.0,
                 filt="bp", f_cutoff=freq*0.8, f_high=freq*1.8, drive=2.0, gain=gain, delay=delay)

def _v_fm(freq, fm_idx=0.4, gain=0.35, cutoff=3500, delay=0.0, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.08, 0.08))
    return Voice(osc="fm", freq=freq, fm_ratio=2.0, fm_index=fm_idx,
                 attack=0.0003, decay_rate=80.0, attack_curve=2.0,
                 filt="lp", f_cutoff=cutoff, drive=1.2, gain=gain, delay=delay)

def _v_housing(freq, gain=0.30, delay=0.0, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.06, 0.06))
    modes = [(freq, 25.0, 1.0), (freq*1.8, 40.0, 0.4), (freq*2.5, 60.0, 0.2)]
    return Voice(osc="modal", modes=modes, attack=0.0008, decay_rate=0.0, attack_curve=1.5,
                 filt="lp", f_cutoff=2500, gain=gain, delay=delay)

def _v_thock(freq, gain=0.45, delay=0.002, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.10, 0.10))
    return Voice(osc="sweep", freq=freq*1.3, freq_end=freq*0.85,
                 attack=0.0015, decay_rate=45.0, attack_curve=2.5,
                 filt="lp", f_cutoff=600, gain=gain, delay=delay)

def _v_sub(freq, gain=0.30, delay=0.003, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.05, 0.05))
    return Voice(osc="sine", freq=freq, attack=0.002, decay_rate=30.0,
                 attack_curve=2.0, filt="lp", f_cutoff=250, gain=gain, delay=delay)

def _v_rattle(lo, hi, gain=0.08, delay=0.002):
    return Voice(osc="noise_white", attack=0.0005, decay_rate=100.0,
                 attack_curve=1.0, filt="bp", f_cutoff=lo, f_high=hi, drive=1.5, gain=gain, delay=delay)

def _v_spring(freq, gain=0.4, delay=0.0, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.08, 0.08))
    mi = rng.uniform(0.8, 1.2) if rng else 1.0
    return Voice(osc="fm", freq=freq, fm_ratio=3.5, fm_index=mi,
                 attack=0.0002, decay_rate=12.0, attack_curve=1.5,
                 filt="lp", f_cutoff=12000, drive=1.0, gain=gain, delay=delay)

def _v_bell(freq, ratios, gain=0.50, decay=4.0, inharmonicity=0.0, rng=None):
    if rng: freq = freq * (2 ** rng.uniform(-0.03, 0.03))
    modes = [(freq * r, decay * (1 + i*0.2), a) for i, (r, a) in enumerate(ratios)]
    return Voice(osc="modal", modes=modes, inharmonicity=inharmonicity,
                 attack=0.0001, decay_rate=0.0, attack_curve=1.0,
                 filt="lp", f_cutoff=16000, gain=gain)

SOUND_PRESETS = {
    "Mechanical": {"desc": "Cherry MX Blue: click jacket, tactile bump, housing resonance"},
    "Cherry MX Red": {"desc": "Linear thock: deep sub-bass, minimal high-frequency transient"},
    "Cherry Brown": {"desc": "Tactile bump: dual-filtered mid-range with smooth decay"},
    "IBM Model M": {"desc": "Buckling spring: metallic ping, membrane snap, housing resonance"},
    "Logitech MX": {"desc": "Scissor switch: shallow, crisp, highly dampened"},
    "Typewriter": {"desc": "Type bar strike with platen resonance and carriage bell"},
    "Cash Register": {"desc": "Mechanical key with drawer mechanism and ka-ching bell"},
    "Bubble Pop": {"desc": "Cavity resonance with pitch sweep and membrane rupture"},
    "Rain Drops": {"desc": "Water droplet modal synthesis with surface tension resonance"},
    "Membrane": {"desc": "Rubber dome collapse with muffled low-frequency resonance"},
    "Crystal": {"desc": "Inharmonic modal bell with stretched partials, long decay"},
    "Wooden": {"desc": "Marimba bar with odd-harmonic modes and resonator coupling"},
    "Soft Foam": {"desc": "Compressed foam thud with damped low-frequency resonance"},
    "Cat Paws": {"desc": "Soft pad impact with fur-damped transients"},
}

CLICK_DURATIONS = {
    "Mechanical": 0.12, "Cherry MX Red": 0.10, "Cherry Brown": 0.09,
    "IBM Model M": 0.25, "Logitech MX": 0.06, "Typewriter": 0.08,
    "Cash Register": 0.12, "Bubble Pop": 0.12, "Rain Drops": 0.10,
    "Membrane": 0.10, "Crystal": 0.40, "Wooden": 0.18, "Soft Foam": 0.18, "Cat Paws": 0.10,
}

def _make_mechanical(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 5000 * (2 ** rng.uniform(-0.12, 0.12))
    voices = [_v_click(cf, 0.55, rng=rng), _v_fm(1200*(2**rng.uniform(-0.08,0.08)), rng.uniform(0.3,0.5), 0.35, 3500, rng=rng),
              _v_housing(400*(2**rng.uniform(-0.06,0.06)), 0.30, rng=rng), _v_thock(150*(2**rng.uniform(-0.10,0.10)), 0.45, 0.002, rng=rng),
              _v_sub(80*(2**rng.uniform(-0.05,0.05)), 0.30, 0.003, rng=rng), _v_rattle(2000, 4000, 0.08, 0.002)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_mechanical_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 3500 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_click(cf, 0.40, rng=rng), _v_fm(800*(2**rng.uniform(-0.08,0.08)), rng.uniform(0.2,0.4), 0.30, 2500, rng=rng),
              _v_housing(300*(2**rng.uniform(-0.06,0.06)), 0.35, rng=rng), _v_thock(120*(2**rng.uniform(-0.10,0.10)), 0.50, 0.002, rng=rng),
              _v_sub(60*(2**rng.uniform(-0.05,0.05)), 0.35, 0.003, rng=rng), _v_rattle(1500, 3000, 0.06, 0.002)]
    return DSP.to_int16(R.render(voices, 0.10, rng))

def _make_mechanical_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 3000 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_click(cf, 0.45, rng=rng), _v_fm(600*(2**rng.uniform(-0.08,0.08)), rng.uniform(0.2,0.4), 0.35, 2500, rng=rng),
              _v_housing(250*(2**rng.uniform(-0.06,0.06)), 0.40, rng=rng), _v_thock(100*(2**rng.uniform(-0.10,0.10)), 0.55, 0.002, rng=rng),
              _v_sub(50*(2**rng.uniform(-0.05,0.05)), 0.40, 0.003, rng=rng), _v_rattle(1200, 2500, 0.07, 0.002)]
    return DSP.to_int16(R.render(voices, 0.10, rng))

def _make_red(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="noise_white", attack=0.0003, decay_rate=250.0, attack_curve=2.0, filt="bp", f_cutoff=1500, f_high=4000, gain=0.15),
              _v_housing(220*(2**rng.uniform(-0.10,0.10)), 0.35, rng=rng), _v_thock(140*(2**rng.uniform(-0.10,0.10)), 0.50, 0.001, rng=rng),
              _v_sub(110*(2**rng.uniform(-0.05,0.05)), 0.35, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_red_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="noise_white", attack=0.0003, decay_rate=200.0, attack_curve=2.0, filt="bp", f_cutoff=1000, f_high=3000, gain=0.12),
              _v_housing(140*(2**rng.uniform(-0.10,0.10)), 0.40, rng=rng), _v_thock(100*(2**rng.uniform(-0.10,0.10)), 0.55, 0.001, rng=rng),
              _v_sub(70*(2**rng.uniform(-0.05,0.05)), 0.40, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.09, rng))

def _make_red_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="noise_white", attack=0.0003, decay_rate=200.0, attack_curve=2.0, filt="bp", f_cutoff=800, f_high=2500, gain=0.12),
              _v_housing(110*(2**rng.uniform(-0.10,0.10)), 0.45, rng=rng), _v_thock(90*(2**rng.uniform(-0.10,0.10)), 0.60, 0.001, rng=rng),
              _v_sub(55*(2**rng.uniform(-0.05,0.05)), 0.45, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.08, rng))

def _make_brown(sr=44100, duration=0.09, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="noise_white", attack=0.0002, decay_rate=300.0, attack_curve=2.5, filt="bp", f_cutoff=2000, f_high=5000, gain=0.20),
              _v_fm(500*(2**rng.uniform(-0.08,0.08)), rng.uniform(0.2,0.35), 0.30, 2500, rng=rng), _v_housing(300*(2**rng.uniform(-0.06,0.06)), 0.35, rng=rng),
              _v_thock(180*(2**rng.uniform(-0.10,0.10)), 0.45, 0.0015, rng=rng), _v_sub(90*(2**rng.uniform(-0.05,0.05)), 0.30, 0.0025, rng=rng)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_brown_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="noise_white", attack=0.0002, decay_rate=250.0, attack_curve=2.5, filt="bp", f_cutoff=1500, f_high=3500, gain=0.15),
              _v_fm(350*(2**rng.uniform(-0.08,0.08)), rng.uniform(0.15,0.3), 0.25, 2000, rng=rng), _v_housing(200*(2**rng.uniform(-0.06,0.06)), 0.40, rng=rng),
              _v_thock(130*(2**rng.uniform(-0.10,0.10)), 0.50, 0.0015, rng=rng), _v_sub(60*(2**rng.uniform(-0.05,0.05)), 0.35, 0.0025, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.07, rng))

def _make_brown_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="noise_white", attack=0.0002, decay_rate=250.0, attack_curve=2.5, filt="bp", f_cutoff=1200, f_high=3000, gain=0.15),
              _v_fm(280*(2**rng.uniform(-0.08,0.08)), rng.uniform(0.15,0.3), 0.30, 2000, rng=rng), _v_housing(160*(2**rng.uniform(-0.06,0.06)), 0.45, rng=rng),
              _v_thock(100*(2**rng.uniform(-0.10,0.10)), 0.55, 0.0015, rng=rng), _v_sub(50*(2**rng.uniform(-0.05,0.05)), 0.40, 0.0025, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.07, rng))

def _make_ibm(sr=44100, duration=0.25, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    pf = 5200 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_spring(pf, 0.40, rng=rng), _v_click(3000*(2**rng.uniform(-0.10,0.10)), 0.45, delay=0.001, rng=rng),
              _v_housing(450*(2**rng.uniform(-0.06,0.06)), 0.30, delay=0.001, rng=rng),
              Voice(osc="fm", freq=800*(2**rng.uniform(-0.08,0.08)), fm_ratio=1.5, fm_index=rng.uniform(0.3,0.5), attack=0.0005, decay_rate=60.0, attack_curve=2.0, filt="lp", f_cutoff=4000, gain=0.25, delay=0.002),
              _v_sub(120*(2**rng.uniform(-0.05,0.05)), 0.35, 0.002, rng=rng),
              Voice(osc="fm", freq=pf*1.5, fm_ratio=2.7, fm_index=rng.uniform(0.6,0.9), attack=0.0003, decay_rate=15.0, attack_curve=1.5, filt="lp", f_cutoff=14000, gain=0.20, delay=0.0005)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_ibm_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    pf = 4800 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_spring(pf, 0.35, rng=rng), _v_click(2500*(2**rng.uniform(-0.10,0.10)), 0.40, delay=0.001, rng=rng),
              _v_housing(380*(2**rng.uniform(-0.06,0.06)), 0.35, delay=0.001, rng=rng),
              Voice(osc="fm", freq=600*(2**rng.uniform(-0.08,0.08)), fm_ratio=1.5, fm_index=rng.uniform(0.3,0.5), attack=0.0005, decay_rate=50.0, attack_curve=2.0, filt="lp", f_cutoff=3500, gain=0.25, delay=0.002),
              _v_sub(100*(2**rng.uniform(-0.05,0.05)), 0.40, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.12, rng))

def _make_ibm_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    pf = 4500 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_spring(pf, 0.45, rng=rng),
              Voice(osc="fm", freq=pf*1.3, fm_ratio=2.7, fm_index=rng.uniform(0.7,0.9), attack=0.0003, decay_rate=14.0, attack_curve=1.5, filt="lp", f_cutoff=13000, gain=0.22, delay=0.0005),
              _v_click(2200*(2**rng.uniform(-0.10,0.10)), 0.42, delay=0.001, rng=rng), _v_housing(320*(2**rng.uniform(-0.06,0.06)), 0.40, delay=0.001, rng=rng),
              _v_thock(100*(2**rng.uniform(-0.10,0.10)), 0.40, 0.002, rng=rng), _v_sub(80*(2**rng.uniform(-0.05,0.05)), 0.40, 0.003, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.15, rng))

def _make_logi(sr=44100, duration=0.06, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 3000 * (2 ** rng.uniform(-0.12, 0.12))
    voices = [_v_click(cf, 0.50, rng=rng),
              Voice(osc="sine", freq=1500*(2**rng.uniform(-0.08,0.08)), attack=0.0002, decay_rate=200.0, attack_curve=2.0, filt="lp", f_cutoff=6000, gain=0.25),
              Voice(osc="noise_white", attack=0.0001, decay_rate=500.0, attack_curve=2.0, filt="lp", f_cutoff=8000, gain=0.15, delay=0.0005)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_logi_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2500 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_click(cf, 0.40, rng=rng),
              Voice(osc="sine", freq=1000*(2**rng.uniform(-0.08,0.08)), attack=0.0002, decay_rate=180.0, attack_curve=2.0, filt="lp", f_cutoff=5000, gain=0.25),
              Voice(osc="noise_white", attack=0.0001, decay_rate=450.0, attack_curve=2.0, filt="lp", f_cutoff=7000, gain=0.12, delay=0.0005)]
    return DSP.to_int16(R.render(voices, 0.05, rng))

def _make_logi_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2200 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_click(cf, 0.42, rng=rng),
              Voice(osc="sine", freq=800*(2**rng.uniform(-0.08,0.08)), attack=0.0002, decay_rate=160.0, attack_curve=2.0, filt="lp", f_cutoff=4000, gain=0.28),
              Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=2.0, filt="lp", f_cutoff=6000, gain=0.12, delay=0.0005)]
    return DSP.to_int16(R.render(voices, 0.05, rng))

def _make_typewriter(sr=44100, duration=0.08, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    sf = 4500 * (2 ** rng.uniform(-0.15, 0.15))
    voices = [Voice(osc="noise_pink", attack=0.001, decay_rate=150.0, attack_curve=1.0, filt="bp", f_cutoff=500, f_high=2000, gain=0.20),
              _v_click(sf, 0.50, delay=0.002, rng=rng),
              Voice(osc="sine", freq=200*(2**rng.uniform(-0.10,0.10)), attack=0.0005, decay_rate=60.0, attack_curve=2.0, filt="lp", f_cutoff=800, gain=0.35, delay=0.002),
              Voice(osc="noise_white", attack=0.001, decay_rate=100.0, attack_curve=1.0, filt="bp", f_cutoff=1500, f_high=3500, gain=0.10, delay=0.003),
              _v_housing(350*(2**rng.uniform(-0.06,0.06)), 0.25, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_typewriter_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    sf = 2000 * (2 ** rng.uniform(-0.12, 0.12))
    voices = [Voice(osc="noise_pink", attack=0.001, decay_rate=120.0, attack_curve=1.0, filt="bp", f_cutoff=400, f_high=1500, gain=0.25),
              _v_click(sf, 0.45, delay=0.002, rng=rng),
              Voice(osc="sine", freq=150*(2**rng.uniform(-0.10,0.10)), attack=0.0005, decay_rate=50.0, attack_curve=2.0, filt="lp", f_cutoff=600, gain=0.40, delay=0.002),
              Voice(osc="noise_white", attack=0.001, decay_rate=80.0, attack_curve=1.0, filt="bp", f_cutoff=1000, f_high=2500, gain=0.12, delay=0.003)]
    return DSP.to_int16(R.render(voices, 0.08, rng))

def _make_typewriter_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    slide = R.render([Voice(osc="noise_white", attack=0.005, decay_rate=20.0, attack_curve=1.0, filt="bp", f_cutoff=200, f_high=800, gain=0.20),
                      Voice(osc="fm", freq=60, fm_ratio=8.0, fm_index=2.0, attack=0.002, decay_rate=12.0, attack_curve=1.0, filt="lp", f_cutoff=2000, gain=0.25)], 0.25, rng)
    bf = 2200 * (2 ** rng.uniform(-0.03, 0.03))
    bell = R.render([_v_bell(bf, [(1.0,1.0),(2.0,0.5),(3.5,0.3),(5.2,0.2),(7.1,0.1)], gain=0.50, decay=4.0, inharmonicity=0.0001, rng=rng),
                     Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=2.0, filt="bp", f_cutoff=bf*0.7, f_high=bf*1.3, drive=2.0, gain=0.15)], 0.40, rng)
    overlap = int(sr * 0.05); total = len(slide) + len(bell) - overlap
    out = np.zeros(total, dtype=np.float64)
    out[:len(slide)] += slide; out[len(slide)-overlap:len(slide)-overlap+len(bell)] += bell
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_cashreg(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2800 * (2 ** rng.uniform(-0.12, 0.12))
    voices = [_v_click(cf, 0.50, rng=rng),
              Voice(osc="fm", freq=800*(2**rng.uniform(-0.08,0.08)), fm_ratio=1.5, fm_index=rng.uniform(0.4,0.6), attack=0.0005, decay_rate=40.0, attack_curve=2.0, filt="lp", f_cutoff=4000, gain=0.30),
              _v_housing(300*(2**rng.uniform(-0.06,0.06)), 0.35, rng=rng), _v_sub(100*(2**rng.uniform(-0.05,0.05)), 0.30, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_cashreg_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    cf = 2000 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_click(cf, 0.45, rng=rng),
              Voice(osc="fm", freq=600*(2**rng.uniform(-0.08,0.08)), fm_ratio=1.5, fm_index=rng.uniform(0.3,0.5), attack=0.0005, decay_rate=35.0, attack_curve=2.0, filt="lp", f_cutoff=3000, gain=0.30),
              _v_housing(220*(2**rng.uniform(-0.06,0.06)), 0.40, rng=rng), _v_sub(80*(2**rng.uniform(-0.05,0.05)), 0.35, 0.002, rng=rng)]
    return DSP.to_int16(R.render(voices, 0.10, rng))

def _make_cashreg_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    press = R.render([_v_click(1500*(2**rng.uniform(-0.10,0.10)), 0.40, rng=rng),
                      Voice(osc="sine", freq=100*(2**rng.uniform(-0.08,0.08)), attack=0.001, decay_rate=150.0, attack_curve=2.0, filt="lp", f_cutoff=500, gain=0.40)], 0.06, rng)
    ka = R.render([Voice(osc="fm", freq=800*(2**rng.uniform(-0.08,0.08)), fm_ratio=1.5, fm_index=rng.uniform(0.4,0.6), attack=0.001, decay_rate=20.0, attack_curve=2.0, filt="lp", f_cutoff=10000, gain=0.35),
                   Voice(osc="noise_white", attack=0.0005, decay_rate=100.0, attack_curve=1.5, filt="bp", f_cutoff=2000, f_high=6000, gain=0.15)], 0.18, rng)
    cf2 = 3500 * (2 ** rng.uniform(-0.03, 0.03))
    ching = R.render([_v_bell(cf2, [(1.0,1.0),(1.5,0.6),(2.0,0.4),(3.0,0.2)], gain=0.45, decay=3.0, rng=rng),
                      Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=2.0, filt="bp", f_cutoff=cf2*0.7, f_high=cf2*1.3, drive=2.0, gain=0.10)], 0.40, rng)
    pause = int(sr * 0.04); total = len(press) + len(ka) + pause + len(ching)
    out = np.zeros(total, dtype=np.float64)
    out[:len(press)] += press; off = len(press); out[off:off+len(ka)] += ka
    off += len(ka) + pause; out[off:off+len(ching)] += ching
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_bubble(sr=44100, duration=0.12, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 800 * (2 ** rng.uniform(-0.20, 0.20))
    voices = [Voice(osc="fm", freq=f0, fm_ratio=1.5, fm_index=rng.uniform(0.3,0.5), attack=0.0005, decay_rate=25.0, attack_curve=3.0, filt="lp", f_cutoff=f0*3, gain=0.45),
              Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=2.0, filt="bp", f_cutoff=f0*0.5, f_high=f0*2, drive=1.5, gain=0.25),
              Voice(osc="sine", freq=f0*0.5, attack=0.001, decay_rate=30.0, attack_curve=2.0, filt="lp", f_cutoff=f0, gain=0.30)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_bubble_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 500 * (2 ** rng.uniform(-0.15, 0.15))
    voices = [Voice(osc="fm", freq=f0, fm_ratio=1.5, fm_index=rng.uniform(0.3,0.5), attack=0.0005, decay_rate=22.0, attack_curve=3.0, filt="lp", f_cutoff=f0*3, gain=0.45),
              Voice(osc="noise_white", attack=0.0001, decay_rate=250.0, attack_curve=2.0, filt="bp", f_cutoff=f0*0.5, f_high=f0*2, drive=1.5, gain=0.22),
              Voice(osc="sine", freq=f0*0.5, attack=0.001, decay_rate=25.0, attack_curve=2.0, filt="lp", f_cutoff=f0, gain=0.30)]
    return DSP.to_int16(R.render(voices, 0.10, rng))

def _make_bubble_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.35); out = np.zeros(n, dtype=np.float64)
    for i in range(3):
        s = int(sr * i * 0.07); f0 = 700 + rng.randint(-150, 150) + i * 50
        pop = R.render([Voice(osc="fm", freq=f0, fm_ratio=1.5, fm_index=0.5, attack=0.0005, decay_rate=25.0, attack_curve=3.0, filt="lp", f_cutoff=f0*3, gain=0.45),
                        Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=2.0, filt="bp", f_cutoff=f0*0.5, f_high=f0*2, drive=1.5, gain=0.20)], 0.08, rng)
        if s + len(pop) <= n: out[s:s+len(pop)] += pop
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_rain(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 3000 * (2 ** rng.uniform(-0.25, 0.25))
    voices = [Voice(osc="noise_white", attack=0.0001, decay_rate=500.0, attack_curve=3.0, filt="bp", f_cutoff=f*0.5, f_high=f*1.5, drive=2.0, gain=0.40),
              Voice(osc="sine", freq=f, attack=0.0002, decay_rate=90.0, attack_curve=2.0, filt="resonator", f_cutoff=f, f_q=3.0, gain=0.35),
              Voice(osc="noise_pink", attack=0.001, decay_rate=70.0, attack_curve=1.5, filt="lp", f_cutoff=5000, gain=0.15, delay=0.002)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_rain_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f = 1800 * (2 ** rng.uniform(-0.20, 0.20))
    voices = [Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=3.0, filt="bp", f_cutoff=f*0.5, f_high=f*1.5, drive=2.0, gain=0.35),
              Voice(osc="sine", freq=f, attack=0.0002, decay_rate=70.0, attack_curve=2.0, filt="resonator", f_cutoff=f, f_q=2.5, gain=0.35),
              Voice(osc="noise_pink", attack=0.001, decay_rate=60.0, attack_curve=1.5, filt="lp", f_cutoff=4000, gain=0.18, delay=0.002)]
    return DSP.to_int16(R.render(voices, 0.07, rng))

def _make_rain_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.30); out = np.zeros(n, dtype=np.float64)
    for i in range(4):
        s = int(sr * (i * 0.06 + rng.uniform(0, 0.02))); f = 2500 + rng.randint(-500, 500)
        drop = R.render([Voice(osc="noise_white", attack=0.0001, decay_rate=500.0, attack_curve=3.0, filt="bp", f_cutoff=f*0.5, f_high=f*1.5, drive=2.0, gain=0.35),
                         Voice(osc="sine", freq=f, attack=0.0002, decay_rate=80.0, attack_curve=2.0, filt="resonator", f_cutoff=f, f_q=3.0, gain=0.30)], 0.05, rng)
        if s + len(drop) <= n: out[s:s+len(drop)] += drop
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_membrane(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=150*(2**rng.uniform(-0.12,0.12)), attack=0.005, decay_rate=45.0, attack_curve=1.5, filt="lp", f_cutoff=800, gain=0.50),
              Voice(osc="noise_white", attack=0.002, decay_rate=200.0, attack_curve=2.0, filt="lp", f_cutoff=2000, gain=0.10),
              Voice(osc="sine", freq=80*(2**rng.uniform(-0.05,0.05)), attack=0.003, decay_rate=35.0, attack_curve=2.0, filt="lp", f_cutoff=300, gain=0.30, delay=0.001)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_membrane_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=100*(2**rng.uniform(-0.10,0.10)), attack=0.006, decay_rate=40.0, attack_curve=1.5, filt="lp", f_cutoff=600, gain=0.55),
              Voice(osc="noise_white", attack=0.002, decay_rate=180.0, attack_curve=2.0, filt="lp", f_cutoff=1500, gain=0.08),
              Voice(osc="sine", freq=50*(2**rng.uniform(-0.05,0.05)), attack=0.004, decay_rate=30.0, attack_curve=2.0, filt="lp", f_cutoff=200, gain=0.35, delay=0.001)]
    return DSP.to_int16(R.render(voices, 0.09, rng))

def _make_membrane_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=90*(2**rng.uniform(-0.10,0.10)), attack=0.006, decay_rate=38.0, attack_curve=1.5, filt="lp", f_cutoff=500, gain=0.55),
              Voice(osc="noise_white", attack=0.002, decay_rate=160.0, attack_curve=2.0, filt="lp", f_cutoff=1200, gain=0.08),
              Voice(osc="sine", freq=45*(2**rng.uniform(-0.05,0.05)), attack=0.004, decay_rate=28.0, attack_curve=2.0, filt="lp", f_cutoff=180, gain=0.40, delay=0.001)]
    return DSP.to_int16(R.render(voices, 0.08, rng))

def _make_crystal(sr=44100, duration=0.40, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 1500 * (2 ** rng.uniform(-0.12, 0.12))
    voices = [_v_bell(f0, [(1.0,1.0),(2.1,0.5),(3.3,0.3),(4.7,0.2),(6.1,0.1)], gain=0.50, decay=7.0, inharmonicity=0.0002, rng=rng),
              Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=3.0, filt="bp", f_cutoff=f0*0.7, f_high=f0*1.3, drive=2.0, gain=0.15)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_crystal_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f0 = 900 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [_v_bell(f0, [(1.0,1.0),(2.1,0.5),(3.3,0.3),(4.7,0.15)], gain=0.50, decay=6.0, inharmonicity=0.0002, rng=rng),
              Voice(osc="noise_white", attack=0.0001, decay_rate=350.0, attack_curve=3.0, filt="bp", f_cutoff=f0*0.7, f_high=f0*1.3, drive=2.0, gain=0.12)]
    return DSP.to_int16(R.render(voices, 0.25, rng))

def _make_crystal_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.7); out = np.zeros(n, dtype=np.float64)
    for i, f0 in enumerate([2200, 2750, 3300]):
        s = int(sr * i * 0.12); f0 += rng.randint(-50, 50)
        chime = R.render([_v_bell(f0, [(1.0,1.0),(2.1,0.5),(3.3,0.3),(4.7,0.2),(6.1,0.1)], gain=0.45, decay=5.0, inharmonicity=0.0002, rng=rng),
                          Voice(osc="noise_white", attack=0.0001, decay_rate=400.0, attack_curve=3.0, filt="bp", f_cutoff=f0*0.7, f_high=f0*1.3, drive=2.0, gain=0.12)], 0.5, rng)
        if s + len(chime) <= n: out[s:s+len(chime)] += chime
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_wooden(sr=44100, duration=0.18, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f1 = 600 * (2 ** rng.uniform(-0.12, 0.12))
    voices = [Voice(osc="modal", modes=[(f1*r, 40*(1+i*0.3), a) for i,(r,a) in enumerate([(1.0,1.0),(3.0,0.4),(5.0,0.2),(7.0,0.1)])], attack=0.0005, decay_rate=0.0, attack_curve=2.0, filt="lp", f_cutoff=8000, gain=0.45),
              Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=3.0, filt="bp", f_cutoff=f1*0.5, f_high=f1*2, drive=1.5, gain=0.25),
              Voice(osc="sine", freq=f1*0.5, attack=0.001, decay_rate=30.0, attack_curve=2.0, filt="lp", f_cutoff=f1, gain=0.25)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_wooden_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    f1 = 400 * (2 ** rng.uniform(-0.10, 0.10))
    voices = [Voice(osc="modal", modes=[(f1*r, 35*(1+i*0.3), a) for i,(r,a) in enumerate([(1.0,1.0),(3.0,0.4),(5.0,0.2)])], attack=0.0005, decay_rate=0.0, attack_curve=2.0, filt="lp", f_cutoff=7000, gain=0.45),
              Voice(osc="noise_white", attack=0.0001, decay_rate=280.0, attack_curve=3.0, filt="bp", f_cutoff=f1*0.5, f_high=f1*2, drive=1.5, gain=0.22),
              Voice(osc="sine", freq=f1*0.5, attack=0.001, decay_rate=28.0, attack_curve=2.0, filt="lp", f_cutoff=f1, gain=0.25)]
    return DSP.to_int16(R.render(voices, 0.12, rng))

def _make_wooden_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.20); out = np.zeros(n, dtype=np.float64)
    for i in range(2):
        s = int(sr * i * 0.09); f1 = 350 + rng.randint(-50, 50)
        knock = R.render([Voice(osc="modal", modes=[(f1*r, 40*(1+j*0.3), a) for j,(r,a) in enumerate([(1.0,1.0),(3.0,0.4),(5.0,0.2)])], attack=0.0005, decay_rate=0.0, attack_curve=2.0, filt="lp", f_cutoff=7000, gain=0.40),
                          Voice(osc="noise_white", attack=0.0001, decay_rate=300.0, attack_curve=3.0, filt="bp", f_cutoff=f1*0.5, f_high=f1*2, drive=1.5, gain=0.22)], 0.08, rng)
        if s + len(knock) <= n: out[s:s+len(knock)] += knock
    return DSP.to_int16(DSP.normalize(out, -1.0))

def _make_foam(sr=44100, duration=0.18, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=100*(2**rng.uniform(-0.12,0.12)), attack=0.01, decay_rate=22.0, attack_curve=1.5, filt="lp", f_cutoff=400, gain=0.50),
              Voice(osc="noise_brown", attack=0.008, decay_rate=25.0, attack_curve=1.5, filt="lp", f_cutoff=800, gain=0.30),
              Voice(osc="sine", freq=50*(2**rng.uniform(-0.05,0.05)), attack=0.012, decay_rate=18.0, attack_curve=1.5, filt="lp", f_cutoff=150, gain=0.35, delay=0.002)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_foam_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=70*(2**rng.uniform(-0.10,0.10)), attack=0.012, decay_rate=20.0, attack_curve=1.5, filt="lp", f_cutoff=300, gain=0.55),
              Voice(osc="noise_brown", attack=0.010, decay_rate=22.0, attack_curve=1.5, filt="lp", f_cutoff=600, gain=0.30),
              Voice(osc="sine", freq=35*(2**rng.uniform(-0.05,0.05)), attack=0.014, decay_rate=15.0, attack_curve=1.5, filt="lp", f_cutoff=120, gain=0.35, delay=0.002)]
    return DSP.to_int16(R.render(voices, 0.14, rng))

def _make_foam_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=60*(2**rng.uniform(-0.10,0.10)), attack=0.012, decay_rate=18.0, attack_curve=1.5, filt="lp", f_cutoff=250, gain=0.55),
              Voice(osc="noise_brown", attack=0.010, decay_rate=20.0, attack_curve=1.5, filt="lp", f_cutoff=500, gain=0.30),
              Voice(osc="sine", freq=30*(2**rng.uniform(-0.05,0.05)), attack=0.014, decay_rate=14.0, attack_curve=1.5, filt="lp", f_cutoff=100, gain=0.40, delay=0.002)]
    return DSP.to_int16(R.render(voices, 0.12, rng))

def _make_catpaw(sr=44100, duration=0.10, seed=0):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=250*(2**rng.uniform(-0.12,0.12)), attack=0.002, decay_rate=70.0, attack_curve=2.5, filt="lp", f_cutoff=1500, gain=0.45),
              Voice(osc="noise_pink", attack=0.002, decay_rate=90.0, attack_curve=2.0, filt="lp", f_cutoff=2000, gain=0.18),
              Voice(osc="sine", freq=120*(2**rng.uniform(-0.05,0.05)), attack=0.003, decay_rate=50.0, attack_curve=2.0, filt="lp", f_cutoff=500, gain=0.30, delay=0.001)]
    return DSP.to_int16(R.render(voices, duration, rng))

def _make_catpaw_space(sr=44100, seed=100):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    voices = [Voice(osc="sine", freq=180*(2**rng.uniform(-0.10,0.10)), attack=0.002, decay_rate=60.0, attack_curve=2.5, filt="lp", f_cutoff=1200, gain=0.45),
              Voice(osc="noise_pink", attack=0.002, decay_rate=80.0, attack_curve=2.0, filt="lp", f_cutoff=1500, gain=0.15),
              Voice(osc="sine", freq=90*(2**rng.uniform(-0.05,0.05)), attack=0.003, decay_rate=45.0, attack_curve=2.0, filt="lp", f_cutoff=400, gain=0.30, delay=0.001)]
    return DSP.to_int16(R.render(voices, 0.08, rng))

def _make_catpaw_enter(sr=44100, seed=200):
    rng = np.random.RandomState(seed); R = SoundRenderer(sr)
    n = int(sr * 0.15); out = np.zeros(n, dtype=np.float64)
    for i in range(2):
        s = int(sr * i * 0.06)
        paw = R.render([Voice(osc="sine", freq=220*(2**rng.uniform(-0.08,0.08)), attack=0.002, decay_rate=70.0, attack_curve=2.5, filt="lp", f_cutoff=1500, gain=0.40),
                        Voice(osc="noise_pink", attack=0.002, decay_rate=90.0, attack_curve=2.0, filt="lp", f_cutoff=2000, gain=0.15)], 0.06, rng)
        if s + len(paw) <= n: out[s:s+len(paw)] += paw
    return DSP.to_int16(DSP.normalize(out, -1.0))

_PRESET_FACTORIES: Dict[str, Dict[str, Callable]] = {
    "Mechanical":    {"click": _make_mechanical,    "space": _make_mechanical_space,    "enter": _make_mechanical_enter},
    "Cherry MX Red": {"click": _make_red,           "space": _make_red_space,           "enter": _make_red_enter},
    "Cherry Brown":  {"click": _make_brown,         "space": _make_brown_space,         "enter": _make_brown_enter},
    "IBM Model M":   {"click": _make_ibm,           "space": _make_ibm_space,           "enter": _make_ibm_enter},
    "Logitech MX":   {"click": _make_logi,          "space": _make_logi_space,          "enter": _make_logi_enter},
    "Typewriter":    {"click": _make_typewriter,    "space": _make_typewriter_space,    "enter": _make_typewriter_enter},
    "Cash Register": {"click": _make_cashreg,       "space": _make_cashreg_space,       "enter": _make_cashreg_enter},
    "Bubble Pop":    {"click": _make_bubble,        "space": _make_bubble_space,        "enter": _make_bubble_enter},
    "Rain Drops":    {"click": _make_rain,          "space": _make_rain_space,          "enter": _make_rain_enter},
    "Membrane":      {"click": _make_membrane,      "space": _make_membrane_space,      "enter": _make_membrane_enter},
    "Crystal":       {"click": _make_crystal,       "space": _make_crystal_space,       "enter": _make_crystal_enter},
    "Wooden":        {"click": _make_wooden,        "space": _make_wooden_space,        "enter": _make_wooden_enter},
    "Soft Foam":     {"click": _make_foam,          "space": _make_foam_space,         "enter": _make_foam_enter},
    "Cat Paws":      {"click": _make_catpaw,        "space": _make_catpaw_space,        "enter": _make_catpaw_enter},
}

if _HAS_NUMBA:
    @numba.njit(cache=True)
    def _nb_mix(mix, flat, offsets, lengths, starts):
        for i in range(len(starts)):
            s = starts[i]; ln = lengths[i]; o = offsets[i]
            for j in range(ln): mix[s + j] += flat[o + j]

    @numba.njit(cache=True)
    def _nb_env_follower(env, attack_coeff, release_coeff):
        n = len(env)
        out = np.empty(n, dtype=np.float64)
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
        out = np.empty(n, dtype=np.float64)
        for i in range(n):
            if smooth_env[i] > target_lin:
                g = 1.0 - (1.0 - 1.0/ratio) * (1.0 - target_lin / smooth_env[i])
            else:
                g = 1.0
            out[i] = x[i] * g
        return out

    @numba.njit(cache=True)
    def _nb_lookahead_gain(smooth_env, target_lin):
        n = len(smooth_env)
        gain = np.ones(n, dtype=np.float64)
        for i in range(n):
            if smooth_env[i] > target_lin:
                gain[i] = target_lin / smooth_env[i]
        return gain

class SimpleSoundGen:
    _PINKY = frozenset("qazp;/`~1!-_=+0)]}\\")
    _RING  = frozenset("wsxol./2@;:'\"3#")
    _THUMB = frozenset(" \t")

    def __init__(self, sr=44100, preset="Mechanical", stereo=False, reverb_amt=0.1):
        self.sr = sr
        self.preset = preset
        self.stereo = stereo
        self.reverb_amt = reverb_amt
        factories = _PRESET_FACTORIES.get(preset, _PRESET_FACTORIES["Mechanical"])
        click_dur = CLICK_DURATIONS.get(preset, 0.06)
        self.clicks = [factories["click"](sr, duration=click_dur, seed=i) for i in range(32)]
        self.spaces = [factories["space"](sr, seed=100+i) for i in range(16)]
        self.enters = [factories["enter"](sr, seed=200+i) for i in range(8)]
        self.releases = [self._make_release_tick(sr, seed=300+i) for i in range(16)]
        self.backspaces = [self._make_backspace_tick(sr, seed=400+i) for i in range(16)]
        if self.reverb_amt > 0:
            self._get_reverb_ir()

    def _make_release_tick(self, sr=44100, seed=0):
        rng = np.random.RandomState(seed)
        R = SoundRenderer(sr)
        voices = [
            Voice(osc="noise_white", attack=0.0001, decay_rate=600.0, attack_curve=2.0,
                  filt="hp", f_cutoff=5000, drive=1.5, gain=0.18),
            Voice(osc="sine", freq=4200*(2**rng.uniform(-0.15, 0.15)),
                  attack=0.0001, decay_rate=350.0, attack_curve=1.5, gain=0.08),
            Voice(osc="sweep", freq=6000, freq_end=3000,
                  attack=0.00005, decay_rate=800.0, attack_curve=2.0,
                  filt="bp", f_cutoff=4000, f_high=8000, gain=0.05, delay=0.0002),
        ]
        return DSP.to_int16(R.render(voices, 0.035, rng))

    def _make_backspace_tick(self, sr=44100, seed=0):
        rng = np.random.RandomState(seed)
        R = SoundRenderer(sr)
        voices = [
            Voice(osc="sweep", freq=250, freq_end=120,
                  attack=0.001, decay_rate=70.0, attack_curve=2.0,
                  filt="lp", f_cutoff=500, gain=0.35),
            Voice(osc="noise_white", attack=0.0002, decay_rate=250.0,
                  attack_curve=2.0, filt="bp", f_cutoff=1200, f_high=3000, gain=0.12)
        ]
        return DSP.to_int16(R.render(voices, 0.05, rng))

    def _get_reverb_ir(self):
        if not hasattr(self, '_ir_l'):
            sr = self.sr
            dur = 1.2 if self.reverb_amt > 0.2 else 0.6
            n = int(sr * dur)
            rng = np.random.RandomState(42)
            t = np.arange(n, dtype=np.float64) / sr
            ir_l = np.zeros(n, dtype=np.float64)
            ir_r = np.zeros(n, dtype=np.float64)
            early_delays = [0.011, 0.013, 0.019, 0.023, 0.029, 0.037,
                            0.041, 0.047, 0.055, 0.063, 0.071, 0.083,
                            0.093, 0.107, 0.121]
            early_gains = [0.85, 0.7, 0.6, 0.55, 0.5, 0.45, 0.4, 0.36,
                           0.32, 0.28, 0.25, 0.22, 0.19, 0.16, 0.13]
            for i, (dt, g) in enumerate(zip(early_delays, early_gains)):
                ds = int(dt * sr)
                if ds < n:
                    if i % 2 == 0:
                        ir_l[ds] += g * (1.0 if rng.rand() > 0.5 else -1.0)
                        ir_r[min(ds + int(0.0015*sr), n-1)] += g * 0.6 * (1.0 if rng.rand() > 0.5 else -1.0)
                    else:
                        ir_r[ds] += g * (1.0 if rng.rand() > 0.5 else -1.0)
                        ir_l[min(ds + int(0.0012*sr), n-1)] += g * 0.6 * (1.0 if rng.rand() > 0.5 else -1.0)
            num_modes = 80
            freqs = rng.uniform(40, 500, num_modes)
            phases = rng.uniform(0, 2*np.pi, num_modes)
            decays = rng.uniform(3.0, 9.0, num_modes)
            tail_l = np.zeros(n, dtype=np.float64)
            tail_r = np.zeros(n, dtype=np.float64)
            for f, p, d in zip(freqs, phases, decays):
                wave = np.sin(2 * np.pi * f * t + p) * np.exp(-t * d)
                tail_l += wave * rng.uniform(0.7, 1.3)
                tail_r += wave * rng.uniform(0.7, 1.3)
            noise_l = rng.randn(n) * np.exp(-t * 12.0) * 0.08
            noise_r = rng.randn(n) * np.exp(-t * 12.0) * 0.08
            ir_l += tail_l * 0.025 + noise_l
            ir_r += tail_r * 0.025 + noise_r
            peak_l = np.max(np.abs(ir_l))
            peak_r = np.max(np.abs(ir_r))
            if peak_l > 0: ir_l /= peak_l
            if peak_r > 0: ir_r /= peak_r
            ir_l = DSP.filt_lp(ir_l, 5500, sr, n_taps=127)
            ir_r = DSP.filt_lp(ir_r, 5500, sr, n_taps=127)
            ir_l = DSP.filt_hp(ir_l, 120, sr, n_taps=63)
            ir_r = DSP.filt_hp(ir_r, 120, sr, n_taps=63)
            predelay = int(sr * 0.008)
            ir_l = np.concatenate([np.zeros(predelay), ir_l])[:n]
            ir_r = np.concatenate([np.zeros(predelay), ir_r])[:n]
            self._ir_l = ir_l
            self._ir_r = ir_r
        return self._ir_l, self._ir_r

    def _pick(self, char, rng):
        if char == "__release__":
            return rng.choice(self.releases), rng.uniform(0.4, 0.6)
        if char == "\b":
            return rng.choice(self.backspaces), rng.uniform(0.7, 0.9)
        if char == "\n":
            return rng.choice(self.enters), rng.uniform(1.05, 1.20)
        elif char == " ":
            return rng.choice(self.spaces), rng.uniform(1.00, 1.15)
        elif char in self._THUMB:
            return rng.choice(self.spaces), rng.uniform(0.90, 1.10)
        elif char.lower() in self._PINKY:
            return rng.choice(self.clicks), rng.uniform(0.75, 0.95)
        elif char.lower() in self._RING:
            return rng.choice(self.clicks), rng.uniform(0.85, 1.05)
        else:
            return rng.choice(self.clicks), rng.uniform(0.95, 1.15)

    def _generate_ambient(self, n, rng, intensity=1.0):
        bed = DSP.noise_pink(n, rng).astype(np.float32) * 0.0008 * intensity
        t = np.arange(n, dtype=np.float64) / self.sr
        drone = np.sin(2*np.pi*58*t + rng.uniform(0, 2*np.pi)) * 0.0004 * intensity
        drone += np.sin(2*np.pi*87*t + rng.uniform(0, 2*np.pi)) * 0.0002 * intensity
        lfo = 0.5 + 0.5 * np.sin(2*np.pi*0.07*t)
        return (bed + drone * lfo).astype(np.float32)

    def generate_pcm(self, timestamps, volume=0.5):
        if not timestamps: return np.zeros(0, dtype=np.int16)
        sr = self.sr
        rng = random.Random(98765)
        all_ts = []
        for ts, ch in timestamps:
            all_ts.append((ts, ch))
            if ch.isalnum() or ch in ".,;[]'":
                release_delay = 0.045 + rng.uniform(0, 0.015)
                all_ts.append((ts + release_delay, "__release__"))
        total = max(ts for ts, _ in all_ts) + 0.3
        n = int(sr * total)
        raw_sounds = []; starts_i = []; pans = []
        for ts, ch in all_ts:
            snd, vm = self._pick(ch, rng)
            s = int(ts * sr)
            if s >= n: continue
            snd_float = snd.astype(np.float32) / 32767.0
            if len(snd_float) == 0: continue
            if self.reverb_amt > 0:
                rev_l = DSP.convolve(snd_float, self._ir_l)
                snd_l = snd_float * (1 - self.reverb_amt * 0.8) + rev_l * (self.reverb_amt * 0.8)
                if self.stereo:
                    rev_r = DSP.convolve(snd_float, self._ir_r)
                    snd_r = snd_float * (1 - self.reverb_amt * 0.8) + rev_r * (self.reverb_amt * 0.8)
                else:
                    snd_r = snd_l
            else:
                snd_l = snd_float
                snd_r = snd_float
            vv = rng.gauss(1.0, 0.05) * vm
            gain_scale = vv ** 0.8
            snd_l *= gain_scale
            snd_r *= gain_scale
            if vv > 1.05:
                drive = (vv - 1.0) * 2.5
                snd_l = np.tanh(snd_l * (1.0 + drive)) / np.tanh(1.0 + drive)
                snd_r = np.tanh(snd_r * (1.0 + drive)) / np.tanh(1.0 + drive)
            snd_l *= volume
            snd_r *= volume
            raw_sounds.append((snd_l, snd_r))
            starts_i.append(s)
            if self.stereo: pans.append(rng.uniform(-0.45, 0.45))
        room_rng = np.random.RandomState(123)
        if not raw_sounds: return np.zeros(n, dtype=np.int16)
        if self.stereo:
            mix_l = np.zeros(n, dtype=np.float32)
            mix_r = np.zeros(n, dtype=np.float32)
            for i, (snd_l, snd_r) in enumerate(raw_sounds):
                s = starts_i[i]; ln = min(len(snd_l), len(snd_r)); pan = pans[i]
                lg = np.cos((pan + 1.0) * np.pi / 4.0)
                rg = np.sin((pan + 1.0) * np.pi / 4.0)
                haas_samp = int(abs(pan) * 0.0006 * self.sr)
                e = min(s + ln, n)
                if pan < 0:
                    mix_l[s:e] += snd_l[:e-s] * lg
                    if s + haas_samp + ln <= n:
                        mix_r[s+haas_samp:s+haas_samp+ln] += snd_r[:ln] * rg
                    else:
                        mix_r[s:e] += snd_r[:e-s] * rg
                else:
                    mix_r[s:e] += snd_r[:e-s] * rg
                    if s + haas_samp + ln <= n:
                        mix_l[s+haas_samp:s+haas_samp+ln] += snd_l[:ln] * lg
                    else:
                        mix_l[s:e] += snd_l[:e-s] * lg
            ambient_l = self._generate_ambient(n, np.random.RandomState(123), 1.0)
            ambient_r = self._generate_ambient(n, np.random.RandomState(456), 1.0)
            mix_l += ambient_l
            mix_r += ambient_r
            mix_l, mix_r = DSP.master_stereo(mix_l.astype(np.float64), mix_r.astype(np.float64), sr)
            out = np.empty(n*2, dtype=np.int16)
            out[0::2] = np.clip(mix_l * 32767, -32768, 32767).astype(np.int16)
            out[1::2] = np.clip(mix_r * 32767, -32768, 32767).astype(np.int16)
            return out
        
        mono_sounds = [s[0] for s in raw_sounds]
        starts = np.array(starts_i, dtype=np.int64)
        lengths = np.array([len(s) for s in mono_sounds], dtype=np.int64)
        flat = np.concatenate(mono_sounds) if mono_sounds else np.array([], dtype=np.float32)
        offsets = np.zeros(len(mono_sounds), dtype=np.int64)
        for i in range(1, len(mono_sounds)): offsets[i] = offsets[i-1] + lengths[i-1]
        mix = np.zeros(n, dtype=np.float32)
        if len(flat) > 0:
            if _HAS_NUMBA:
                _nb_mix(mix, flat, offsets, lengths, starts)
            else:
                for i in range(len(starts)):
                    s = int(starts[i]); ln = int(lengths[i]); o = int(offsets[i])
                    mix[s:s+ln] += flat[o:o+ln]
        ambient = self._generate_ambient(n, room_rng, 1.0)
        mix += ambient
        mix = DSP.master_mono(mix.astype(np.float64), sr)
        return np.clip(mix * 32767.0, -32768, 32767).astype(np.int16)

    def generate_track(self, timestamps, filepath, volume=0.5):
        if not timestamps: return
        pcm = self.generate_pcm(timestamps, volume)
        if len(pcm) == 0: return
        channels = 2 if self.stereo else 1
        with wave.open(filepath, "w") as wf:
            wf.setnchannels(channels); wf.setsampwidth(2); wf.setframerate(self.sr)
            wf.writeframes(pcm.tobytes())

def _pcm_to_wav_bytes(pcm, sr=44100, channels=1):
    buf = io.BytesIO()
    with wave.open(buf, "w") as wf:
        wf.setnchannels(channels); wf.setsampwidth(2); wf.setframerate(sr)
        wf.writeframes(pcm.tobytes())
    return buf.getvalue()

# =====================================================================
# 6. KEYBOARD LAYOUTS & OVERLAY
# =====================================================================
_US_SHIFT = {"~":"`","!":"1","@":"2","#":"3","$":"4","%":"5","^":"6","&":"7",
             "*":"8","(":"9",")":"0","_":"-","+":"=","{":"[","}":"]",
             "|":"\\",":":";",'"':"'","<":",",">":".","?":"/"}

_QWERTY_ROWS = [
    [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
    [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],
    [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],
    [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],
    [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
]

_DVORAK_ROWS = [
    [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("[",1),("]",1),("Bksp",2)],
    [("Tab",1.5),("'",1),(",",1),(".",1),("P",1),("Y",1),("F",1),("G",1),("C",1),("R",1),("L",1),("/",1),("=",1),("\\",1.5)],
    [("Caps",1.75),("A",1),("O",1),("E",1),("U",1),("I",1),("D",1),("H",1),("T",1),("N",1),("S",1),("-",1),("Enter",2.25)],
    [("Shift",2.25),(";",1),("Q",1),("J",1),("K",1),("X",1),("B",1),("M",1),("W",1),("V",1),("Z",1),("Shift",2.75)],
    [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
]

_COLEMAK_ROWS = [
    [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
    [("Tab",1.5),("Q",1),("W",1),("F",1),("P",1),("G",1),("J",1),("L",1),("U",1),("Y",1),(";",1),("[",1),("]",1),("\\",1.5)],
    [("Bksp",1.75),("A",1),("R",1),("S",1),("T",1),("D",1),("H",1),("N",1),("E",1),("I",1),("O",1),("'",1),("Enter",2.25)],
    [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("K",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],
    [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
]

KEYBOARD_LAYOUTS: Dict[str, Dict] = {
    "QWERTY":  {"description": "Standard US QWERTY layout",  "rows": _QWERTY_ROWS,  "shift_map": _US_SHIFT},
    "Dvorak":  {"description": "Dvorak ergonomic layout",     "rows": _DVORAK_ROWS, "shift_map": _US_SHIFT},
    "Colemak": {"description": "Colemak ergonomic layout",    "rows": _COLEMAK_ROWS,"shift_map": _US_SHIFT},
}

def _build_char_map(layout_name):
    ld = KEYBOARD_LAYOUTS[layout_name]
    cm = {}
    for ri, row in enumerate(ld["rows"]):
        for ci, (label, w) in enumerate(row):
            ll = label.lower()
            if len(label) == 1:
                cm[label] = (ri, ci); cm[label.lower()] = (ri, ci); cm[label.upper()] = (ri, ci)
            if ll == "space" or (label == "" and w >= 4): cm[" "] = (ri, ci)
            elif "enter" in ll: cm["\n"] = (ri, ci)
            elif "tab" in ll: cm["\t"] = (ri, ci)
            elif "bksp" in ll: cm["\x08"] = (ri, ci)
    for shifted, base in ld.get("shift_map", {}).items():
        if base in cm: cm[shifted] = cm[base]
    return cm

class KeyboardOverlay:
    def __init__(self, video_w, video_h, layout_name="QWERTY", theme=None,
                 opacity=0.82, max_height=None, position="bottom_center"):
        self.video_w = video_w; self.video_h = video_h
        self.layout_name = layout_name; self.theme = theme
        self.opacity = opacity; self.rows = KEYBOARD_LAYOUTS[layout_name]["rows"]
        self.char_map = _build_char_map(layout_name)
        self.num_rows = len(self.rows); self.position = position
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
                    if th > max_height: hi = mid
                    else: lo = mid
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
        self.key_rects = {}
        self._rebuild_key_rects()
        self._bg_cache = None

    def height_needed(self):
        return self._kb_height + max(8, self.video_h // 60) + max(6, self.video_h // 90)

    def _apply_position(self):
        m = max(8, self.video_h // 60)
        vw, vh, kw, kh = self.video_w, self.video_h, self._kb_width, self._kb_height
        pos = self.position
        if pos == "bottom_center": self._kb_x = (vw-kw)//2; self._kb_y = vh-kh-m
        elif pos == "bottom_right": self._kb_x = vw-kw-m; self._kb_y = vh-kh-m
        elif pos == "bottom_left": self._kb_x = m; self._kb_y = vh-kh-m
        elif pos == "top_center": self._kb_x = (vw-kw)//2; self._kb_y = m
        elif pos == "top_right": self._kb_x = vw-kw-m; self._kb_y = m
        elif pos == "top_left": self._kb_x = m; self._kb_y = m
        elif pos == "center_left": self._kb_x = m; self._kb_y = (vh-kh)//2
        elif pos == "center_right": self._kb_x = vw-kw-m; self._kb_y = (vh-kh)//2

    def _rebuild_key_rects(self):
        self.key_rects = {}
        for ri, row in enumerate(self.rows):
            x = self._kb_x
            for ci, (_, w) in enumerate(row):
                kw = int(w * self.key_unit) - self.key_gap
                y = self._kb_y + ri * (self.key_h + self.key_gap)
                self.key_rects[(ri, ci)] = QRect(x, y, kw, self.key_h)
                x += int(w * self.key_unit)
        self._bg_cache = None

    def reposition(self, y_below=0):
        self._apply_position(); self._rebuild_key_rects()

    def resolve_key(self, ch):
        return self.char_map.get(ch)

    def _build_bg_cache(self):
        pad = max(6, self.key_unit // 4)
        w = self._kb_width + 2 * pad
        h = self._kb_height + 2 * pad
        self._bg_cache = QPixmap(w, h)
        self._bg_cache.fill(Qt.transparent)
        p = QPainter(self._bg_cache)
        p.setRenderHint(QPainter.Antialiasing)
        th = self.theme or THEMES["Dracula"]
        radius = max(3, self.key_unit // 8)
        bg = QColor(th["background"])
        p.setPen(QPen(QColor(th["window_border"]), max(1, self.key_unit // 20)))
        p.setBrush(bg)
        p.drawRoundedRect(0, 0, w, h, radius*2, radius*2)
        key_bg = QColor(th["title_bar"])
        key_border = QColor(th["window_border"])
        label_color = QColor(th["foreground"])
        mod_color = QColor(th["line_number"])
        p.setFont(QFont("Segoe UI", max(7, int(self.key_unit * 0.30))))
        for (ri, ci), rect in self.key_rects.items():
            label = self.rows[ri][ci][0]
            cache_rect = QRect(rect.x() - self._kb_x + pad, rect.y() - self._kb_y + pad, rect.width(), rect.height())
            p.setBrush(key_bg)
            p.setPen(key_border)
            p.drawRoundedRect(cache_rect, radius, radius)
            if label:
                is_mod = len(label) > 1
                p.setPen(mod_color if is_mod else label_color)
                p.drawText(cache_rect, Qt.AlignCenter, label)
        p.end()

    def draw(self, painter, active_key=None, flash=0.0):
        painter.save()
        painter.setOpacity(self.opacity)
        if self._bg_cache is None:
            self._build_bg_cache()
        pad = max(6, self.key_unit // 4)
        painter.drawPixmap(self._kb_x - pad, self._kb_y - pad, self._bg_cache)
        if flash > 0 and active_key is not None:
            th = self.theme or THEMES["Dracula"]
            try: hl_base = QColor(th["cursor"])
            except: hl_base = QColor("#89b4fa")
            key_bg = QColor(th["title_bar"])
            hl_fill = QColor(int(key_bg.red()+(hl_base.red()-key_bg.red())*flash),
                             int(key_bg.green()+(hl_base.green()-key_bg.green())*flash),
                             int(key_bg.blue()+(hl_base.blue()-key_bg.blue())*flash))
            hl_glow = QColor(hl_base); hl_glow.setAlpha(int(60 * flash))
            hl_expand = max(3, int(self.key_unit * 0.12 * flash))
            rect = self.key_rects[active_key]
            radius = max(3, self.key_unit // 8)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(hl_glow)
            painter.drawRoundedRect(rect.adjusted(-hl_expand,-hl_expand,hl_expand,hl_expand), radius, radius)
            painter.setBrush(hl_fill)
            painter.setPen(QColor(th["window_border"]))
            painter.drawRoundedRect(rect, radius, radius)
            label = self.rows[active_key[0]][active_key[1]][0]
            if label:
                is_mod = len(label) > 1
                painter.setPen(QColor(th["foreground"]) if not is_mod else QColor(th["line_number"]))
                painter.setFont(QFont("Segoe UI", max(7, int(self.key_unit * 0.30))))
                painter.drawText(rect, Qt.AlignCenter, label)
        painter.restore()

# =====================================================================
# 7. TYPING ANIMATOR
# =====================================================================
Event = Tuple[float, int, str]
_QWERTY_ROWS_STR = ("`1234567890-=", "qwertyuiop[]\\", "asdfghjkl;'", "zxcvbnm,./")
_QWERTY_POS: Dict[str, Tuple[int, int]] = {}
for _r, _row in enumerate(_QWERTY_ROWS_STR):
    for _c, _ch in enumerate(_row):
        _QWERTY_POS[_ch] = (_r, _c)
for _ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
    _QWERTY_POS[_ch] = _QWERTY_POS.get(_ch.lower(), (2, 0))

NEIGHBORS = {
    'a':'sqz','b':'vn','c':'vx','d':'sf','e':'wr','f':'dg','g':'fh','h':'gj',
    'i':'uo','j':'hk','k':'jl','l':'k','m':'n','n':'bm','o':'ip','p':'o',
    'q':'w','r':'et','s':'ad','t':'ry','u':'yi','v':'cb','w':'qe','x':'zc',
    'y':'tu','z':'x',
}

@dataclass
class TypingProfile:
    name: str = "junior"
    wpm: int = 90
    typo_rate: float = 0.028
    pause_freq: float = 0.15
    burst_chance: float = 0.15
    start_pause: float = 0.5
    end_pause: float = 1.5
    auto_indent: bool = True

JUNIOR_PROFILE = TypingProfile(
    name="Junior Dev", wpm=90, typo_rate=0.028, pause_freq=0.15,
    burst_chance=0.15, start_pause=0.5, end_pause=1.5, auto_indent=True,
)

SENIOR_PROFILE = TypingProfile(
    name="Senior Dev", wpm=130, typo_rate=0.005, pause_freq=0.05,
    burst_chance=0.35, start_pause=0.3, end_pause=1.0, auto_indent=True,
)

class TypingAnimator:
    def __init__(self, code: str, profile: TypingProfile, seed: Optional[int] = None):
        self.code = code
        self.profile = profile
        cps = (profile.wpm * 5) / 60
        self.base_delay = 1.0 / cps
        self.display_chars: List[str] = []
        self.text_snapshots: List[str] = []
        self.error_snapshots: List[List[bool]] = []
        self.typo_count: int = 0
        self.timeline: List[Event] = self._build(seed if seed is not None else 42)
        self._timestamps = [ts for ts, _, _ in self.timeline]

    def _wrong_char(self, correct: str, rng: random.Random) -> str:
        lower = correct.lower()
        if lower in NEIGHBORS:
            wrong = rng.choice(NEIGHBORS[lower])
            return wrong.upper() if correct.isupper() else wrong
        return chr(ord(correct) + rng.choice([-1, 1]))

    def _build(self, seed) -> List[Event]:
        rng = random.Random(seed)
        t = self.profile.start_pause
        events: List[Event] = []
        p = self.profile
        i = 0
        current_text = []
        current_errors = []
        self.text_snapshots.append("")
        self.error_snapshots.append([])

        def take_snapshot():
            self.text_snapshots.append("".join(current_text))
            self.error_snapshots.append(list(current_errors))

        while i < len(self.code):
            ch = self.code[i]
            d = self.base_delay * rng.uniform(0.6, 1.4)
            if ch == "\n": d *= rng.uniform(2.0, 4.0)
            elif ch == " ": d *= rng.uniform(0.7, 1.3)
            elif ch == "\t": d *= rng.uniform(1.2, 1.8)
            elif ch in "([{": d *= rng.uniform(1.1, 1.8)
            elif ch in ")]}": d *= rng.uniform(0.9, 1.5)
            elif ch in ",;:": d *= rng.uniform(1.3, 2.2)
            if i >= 1:
                prev = self.code[i - 1]
                pa = _QWERTY_POS.get(prev.lower())
                pb = _QWERTY_POS.get(ch.lower())
                if pa and pb:
                    dist = math.hypot(pa[0] - pb[0], pa[1] - pb[1])
                    if dist < 0.5: d *= 0.7
                    elif dist > 4: d *= 1.15
            if ch == ":" and i > 0:
                prev_code = self.code[max(0, i-10):i]
                if "def " in prev_code or "class " in prev_code:
                    if rng.random() < 0.6:
                        d += rng.uniform(2.0, 5.0)
            elif ch == ":":
                if rng.random() < 0.2:
                    d += rng.uniform(1.0, 2.5)
            if ch == "\n" or ch == ":":
                if rng.random() < p.pause_freq: d += rng.uniform(0.4, 1.2)
            elif rng.random() < (p.pause_freq * 0.2): d += rng.uniform(0.3, 0.8)
            if rng.random() < 0.012: d += rng.uniform(0.4, 1.4)
            
            burst_active = False
            if ch.isalpha() and rng.random() < p.burst_chance and i + 1 < len(self.code):
                burst_len = rng.randint(4, 9)
                burst_chars = []
                for bi in range(burst_len):
                    if i + bi >= len(self.code): break
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
                if (p.typo_rate > 0 and rng.random() < p.typo_rate and
                    ch.isalpha() and i < len(self.code) - 1 and
                    ch not in (' ', '\n', '\t')):
                    self.typo_count += 1
                    typo_len = rng.choices([1, 2, 3], weights=[70, 20, 10])[0]
                    for _ in range(typo_len):
                        wrong = self._wrong_char(ch, rng)
                        current_text.append(wrong)
                        current_errors.append(True)
                        self.display_chars.append(wrong)
                        events.append((t, len(self.display_chars) - 1, wrong))
                        take_snapshot()
                        t += max(d * 0.5, 0.012)
                    t += rng.uniform(0.15, 0.4)
                    for _ in range(typo_len):
                        current_text.pop()
                        current_errors.pop()
                        self.display_chars.append("\b")
                        events.append((t, len(self.display_chars) - 1, "\b"))
                        take_snapshot()
                        t += max(d * 0.4, 0.012)
                
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
        if not self.timeline: return self.profile.start_pause + self.profile.end_pause
        return self.timeline[-1][0] + self.profile.end_pause

    def visible_at(self, t: float) -> int:
        if t < self.profile.start_pause: return 0
        idx = bisect.bisect_right(self._timestamps, t)
        if idx == 0: return 0
        return self.timeline[idx - 1][1] + 1

    def char_timestamps(self) -> List[Tuple[float, str]]:
        return [(ts, ch) for ts, _, ch in self.timeline if ch != "\b"]

    def active_key_at(self, t: float, flash_duration: float = 0.18):
        if not self._timestamps: return (None, 0.0)
        idx = bisect.bisect_right(self._timestamps, t)
        if idx == 0: return (None, 0.0)
        char = self.timeline[idx - 1][2]
        dt = t - self.timeline[idx - 1][0]
        if dt < flash_duration:
            return (char, max(0.0, 1.0 - dt / flash_duration))
        return (None, 0.0)

    @staticmethod
    def estimate_duration(code, wpm, start_pause, end_pause, typo_rate=0.0):
        cps = (wpm * 5) / 60
        base_delay = 1.0 / cps
        total = 0.0
        for ch in code:
            d = base_delay
            if ch == "\n": d *= 3.0
            elif ch == "\t": d *= 1.5
            elif ch in "([{": d *= 1.45
            elif ch in ")]}": d *= 1.2
            elif ch in ",;:": d *= 1.75
            d += 0.011
            if typo_rate > 0 and ch.isalpha(): d += typo_rate * (d + 0.6)
            d = max(d, 0.012)
            total += d
        return total + start_pause + end_pause

# =====================================================================
# 8. CODE RENDERER
# =====================================================================
class CodeRenderer:
    TOKEN_COLOR_MAP = {
        "keyword": "keyword", "builtin": "builtin", "string": "string",
        "number": "number", "comment": "comment", "decorator": "decorator",
        "function": "function", "class_name": "class_name", "operator": "operator",
    }
    CURSOR_BLINK = 0.53

    def __init__(self, width, height, theme_name="Dracula", font_family="Consolas",
                 font_size=22, show_line_numbers=True, show_window_chrome=True,
                 padding=24, tab_size=4, title_text="main.py", language="Python",
                 keyboard_overlay=None, bg_image_path=None, total_code_lines=0,
                 cursor_glow=True, show_watermark=False, accent_color=None):
        self.width = width; self.height = height
        self.theme = THEMES.get(theme_name, THEMES["Dracula"])
        self.font_family = font_family; self.font_size = font_size
        self.show_line_numbers = show_line_numbers
        self.show_window_chrome = show_window_chrome
        self.padding = padding; self.tab_size = tab_size
        self.title_text = title_text; self.language = language
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
            if f in _available: chosen = f; break
        self.font = QFont(chosen, font_size)
        self.font.setFamilies(_families)
        self.font.setFixedPitch(True)
        self.fm = QFontMetrics(self.font)
        self.char_w = self.fm.horizontalAdvance("M")
        self.line_h = self.fm.height()
        
        self._qcolors = {}
        for key, val in self.theme.items():
            if isinstance(val, str) and val.startswith("#"):
                self._qcolors[key] = QColor(val)
        self._qc_fg = self._qcolors.get("foreground", QColor("#f8f8f2"))
        self._qc_ln = self._qcolors.get("line_number", QColor("#6272a4"))
        self._qc_ln_active = QColor(self._qc_fg).darker(120)
        self._qc_cursor = self._qcolors.get("cursor", QColor("#f8f8f2"))
        self._qc_current_line = self._qcolors.get("current_line", QColor("#44475a"))
        self._qc_accent = QColor(self.accent_color)
        
        self.bg_image = QPixmap(bg_image_path) if bg_image_path and os.path.exists(bg_image_path) else None
        self._build_bg_cache()
        
        self._cached_id = 0; self._cached_len = 0
        self._cached_resolved = ""; self._cached_colors = []
        self._cached_color_qc = []; self._cached_is_clean = []; self._cached_stack_len = []
        self._dirty_nv = -1; self._dirty_text = ""; self._dirty_qc = []
        self._layout_nv = -1; self._layout_lines = []; self._layout_offsets = []
        self._layout_cursor_line = 0
        self._line_cache = OrderedDict()
        self._tab_advance = self.char_w * self.tab_size
        
        self._full_code = ""
        self._full_code_colors = []
        self._tok_cache = OrderedDict()

    def set_full_code(self, code: str):
        """Pre-tokenize the full code for fast incremental rendering."""
        self._full_code = code
        self._full_code_colors = self._tokenize_to_colors(code)

    @staticmethod
    def auto_font_size(code_lines, width, height, padding=24, show_chrome=True,
                       show_ln=True, tab_size=4, code=None, font_family="Consolas", keyboard_h=0):
        chrome_h = 42 if show_chrome else 0
        kb_used = min(keyboard_h, (height - 2*padding)//3) if keyboard_h > 0 else 0
        rect_h = height - 2*padding - kb_used - chrome_h
        rect_w = width - 2*padding - 8
        if rect_h < 20 or rect_w < 40 or code_lines < 1: return 14
        max_chars = 80
        if code:
            longest = max(len(line.replace("\t"," "*tab_size)) for line in code.split("\n"))
            max_chars = max(longest, 1)
        def _ln_w(cw): return (len(str(code_lines))*cw + 16) if show_ln else 0
        max_font = max(14, min(48, int(width/80)))
        target_vis = min(code_lines, 35)
        max_check = min(max_chars, 120)
        lo, hi, best = 8, max_font, 14
        while lo <= hi:
            mid = (lo + hi) // 2
            fm = QFontMetrics(QFont(font_family, mid))
            lh = fm.height()
            if target_vis * lh <= rect_h:
                cw = fm.horizontalAdvance("M")
                lw = max_check * cw + _ln_w(cw)
                if lw <= rect_w: best = mid; lo = mid + 1
                else: hi = mid - 1
            else: hi = mid - 1
        return max(8, best)

    @staticmethod
    def _resolve_backspaces(chars):
        out = []
        for ch in chars:
            if ch == "\b":
                if out: out.pop()
            else: out.append(ch)
        return "".join(out)

    @staticmethod
    def _precompute_clean(display_chars, resolved):
        n = len(display_chars)
        is_clean = [True] * (n + 1)
        stack_len = [0] * (n + 1)
        is_error = [False] * n
        stack = []; incorrect = 0; rlen = len(resolved)
        for i in range(n):
            ch = display_chars[i]
            if ch == "\b":
                if stack:
                    _, wc = stack.pop()
                    if not wc: incorrect -= 1
            else:
                pos = len(stack)
                wc = pos < rlen and ch == resolved[pos]
                stack.append((i, wc))
                if not wc:
                    incorrect += 1
                    is_error[i] = True
            is_clean[i+1] = (incorrect == 0)
            stack_len[i+1] = len(stack)
        return is_clean, stack_len, is_error

    def _get_cache(self, full_text):
        cid = id(full_text); clen = len(full_text)
        if cid != self._cached_id or clen != self._cached_len:
            resolved = self._resolve_backspaces(full_text)
            self._cached_resolved = resolved
            self._cached_colors = self._tokenize_to_colors(resolved)
            fg = self._qc_fg; qc = self._qcolors
            self._cached_color_qc = [qc.get(ck, fg) for ck in self._cached_colors]
            self._cached_is_clean, self._cached_stack_len, self._cached_is_error = self._precompute_clean(full_text, resolved)
            self._cached_id = cid; self._cached_len = clen
            self._dirty_nv = -1
        return (self._cached_resolved, self._cached_colors, self._cached_color_qc,
                self._cached_is_clean, self._cached_stack_len, self._cached_is_error)

    def _get_line_layout(self, line):
        cached = self._line_cache.get(line)
        if cached is not None: return cached
        char_x = []; x = 0; tab = self._tab_advance; ham = self.fm.horizontalAdvance
        for ch in line:
            char_x.append(x)
            x += tab if ch == "\t" else ham(ch)
        if len(self._line_cache) >= 512: self._line_cache.popitem(last=False)
        self._line_cache[line] = char_x
        return char_x

    def _tokenize_to_colors(self, text):
        cached = self._tok_cache.get(text)
        if cached is not None:
            return cached
        tokens = Tokenizer.tokenize(text, self.language)
        colors = ["foreground"] * len(text)
        pos = 0; get = self.TOKEN_COLOR_MAP.get; n = len(colors)
        for ttype, ttxt in tokens:
            ckey = get(ttype, "foreground")
            end = min(pos + len(ttxt), n)
            colors[pos:end] = [ckey] * (end - pos)
            pos = end
        if len(self._tok_cache) > 256:
            self._tok_cache.popitem(last=False)
        self._tok_cache[text] = colors
        return colors

    def _build_bg_cache(self):
        self._bg = QImage(self.width, self.height, QImage.Format_RGB32)
        self._bg.fill(QColor(self.theme["background"]))
        p = QPainter(self._bg)
        p.setRenderHint(QPainter.Antialiasing)
        if self.bg_image:
            scaled = self.bg_image.scaled(self.width, self.height,
                                          Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                          Qt.TransformationMode.SmoothTransformation)
            x = (self.width - scaled.width()) // 2
            y = (self.height - scaled.height()) // 2
            p.drawPixmap(x, y, scaled)
            p.fillRect(0, 0, self.width, self.height, QColor(0, 0, 0, 130))
        else:
            bg = self._qcolors.get("background", QColor("#282a36"))
            g = QLinearGradient(0, 0, 0, self.height)
            g.setColorAt(0, bg.lighter(105)); g.setColorAt(1, bg)
            p.fillRect(0, 0, self.width, self.height, g)
        
        w, h = self.width, self.height; pad = self.padding
        chrome_h = 42 if self.show_window_chrome else 0
        kb_reserve = 0
        if self.keyboard_overlay:
            kb_reserve = min(self.keyboard_overlay.height_needed(), (h - 2*pad) // 3)
        wx, wy = pad, pad
        ww = w - 2*pad; wh = h - 2*pad - kb_reserve
        p.setPen(Qt.PenStyle.NoPen)
        for s in range(6, 0, -1):
            alpha = int(40 - s * 5)
            p.setBrush(QColor(0, 0, 0, alpha))
            p.drawRoundedRect(wx - s, wy - s + (s//2), ww + 2*s, wh + 2*s, 12 + s, 12 + s)
        p.setPen(QColor(self.theme["window_border"]))
        p.setBrush(QColor(self.theme["background"]))
        p.drawRoundedRect(wx, wy, ww, wh, 12, 12)
        if self.show_window_chrome:
            p.setPen(Qt.PenStyle.NoPen); p.setBrush(QColor(self.theme["title_bar"]))
            p.drawRoundedRect(wx, wy, ww, chrome_h, 12, 12)
            p.drawRect(wx, wy + chrome_h - 12, ww, 12)
            for i, color in enumerate(["#ff5f56", "#ffbd2e", "#27c93f"]):
                cx = wx + 20 + i * 24
                p.setBrush(QColor(color)); p.setPen(Qt.PenStyle.NoPen)
                p.drawEllipse(QPoint(cx, wy + 19), 7, 7)
            p.setPen(QColor(self.theme["title_text"]))
            p.setFont(QFont(self.font_family, 12))
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

    def render_frame(self, visible_text, vis_err, cursor_visible=True,
                     target=None, active_char=None, key_flash=0.0):
        img = target if target is not None else QImage(self.width, self.height, QImage.Format_RGB32)
        if target is None: img.fill(QColor(self.theme["background"]))
        p = QPainter(img)
        p.setRenderHint(QPainter.TextAntialiasing)
        p.drawImage(0, 0, self._bg)
        cr = self._code_rect
        
        if self._full_code_colors and visible_text == self._full_code[:len(visible_text)]:
            colors = self._full_code_colors[:len(visible_text)]
        else:
            colors = self._tokenize_to_colors(visible_text)
        fg = self._qc_fg; qc = self._qcolors
        vis_qc = [qc.get(ck, fg) for ck in colors]
        
        if visible_text != self._layout_nv:
            self._layout_lines = visible_text.split("\n")
            offsets = []; off = 0
            for ln in self._layout_lines:
                offsets.append(off); off += len(ln) + 1
            self._layout_offsets = offsets
            self._layout_cursor_line = visible_text.count("\n")
            self._layout_nv = visible_text
        
        lines = self._layout_lines; line_offsets = self._layout_offsets
        cursor_line = self._layout_cursor_line
        total_lines = len(lines)
        cr_h = cr.height(); cr_top = cr.top()
        max_vis = max(1, -(-cr_h // self.line_h))
        lh_base = self.line_h
        scroll = 0
        if cursor_line >= scroll + max_vis - min(5, max_vis - 1):
            scroll = max(0, cursor_line - max_vis + min(5, max_vis - 1) + 1)
        if cursor_line < scroll + 3:
            scroll = max(0, cursor_line - 3)
        max_scroll = max(0, total_lines - max_vis)
        if scroll > max_scroll: scroll = max_scroll
        ln_width = (len(str(total_lines + scroll)) * self.char_w + 16) if self.show_line_numbers else 0
        current_scroll_line = cursor_line - scroll
        line_y_arr = []; line_h_arr = []; y_acc = cr_top
        for si in range(max_vis):
            li = scroll + si
            if li >= total_lines: break
            line_y_arr.append(y_acc); line_h_arr.append(lh_base); y_acc += lh_base
        n_drawn = len(line_y_arr)
        if 0 <= current_scroll_line < n_drawn:
            p.fillRect(cr.left(), line_y_arr[current_scroll_line], cr.width(),
                       line_h_arr[current_scroll_line], self._qc_current_line)
            p.setPen(QPen(self._qc_accent, 2))
            p.drawLine(cr.left(), line_y_arr[current_scroll_line],
                       cr.left(), line_y_arr[current_scroll_line] + line_h_arr[current_scroll_line])
        if self.show_line_numbers and ln_width > 0:
            sep_x = cr.left() + ln_width
            sc = QColor(self._qc_ln); sc.setAlpha(60)
            p.setPen(QPen(sc, 1)); p.drawLine(sep_x, cr.top(), sep_x, cr.top() + max_vis * lh_base)
        p.setClipRect(cr); p.setFont(self.font)
        x0 = cr.left() + ln_width
        n_vis_chars = len(visible_text)
        typed_lines_count = visible_text.count("\n") + 1
        for si in range(n_drawn):
            li = scroll + si; lh = line_h_arr[si]; y = line_y_arr[si]
            global_off = line_offsets[li]
            if self.show_line_numbers:
                if li + 1 <= typed_lines_count:
                    color = self._qc_ln_active if li == cursor_line else self._qc_ln
                else:
                    color = QColor(self._qc_ln)
                    color.setAlpha(40)
                p.setPen(color)
                p.drawText(QRect(cr.left(), y, ln_width, lh), Qt.AlignRight | Qt.AlignVCenter, str(li + 1))
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
                        for uw_x in range(ux_start, ux_end, uw_step):
                            path.lineTo(uw_x + uw_step/2, uw_y - 3)
                            path.lineTo(uw_x + uw_step, uw_y)
                        p.drawPath(path)
                    cur_qc = next_qc; cur_err = next_err; run_start = j
            if cursor_visible and li == cursor_line:
                n_ch = len(line)
                if n_ch < len(char_x):
                    cx = char_x[n_ch]
                    self._draw_caret(p, int(x0 + cx), int(y + lh * 0.15), max(4, lh - 10))
                else:
                    last_x = char_x[-1] if char_x else 0
                    last_char = line[-1] if line else " "
                    last_w = self._tab_advance if last_char == "\t" else self.fm.horizontalAdvance(last_char)
                    cx = last_x + last_w
                    self._draw_caret(p, int(x0 + cx), int(y + lh * 0.15), max(4, lh - 10), " ")
        p.setClipping(False)
        if self.keyboard_overlay:
            ak = None; kf = 0.0
            if active_char is not None and key_flash > 0:
                ak = self.keyboard_overlay.resolve_key(active_char); kf = key_flash
            self.keyboard_overlay.draw(p, active_key=ak, flash=kf)
        if self.show_watermark:
            wm_font = QFont(self.font_family, max(8, self.font_size // 3))
            p.setFont(wm_font); p.setPen(QColor(self._qc_ln))
            wm = f"{datetime.now().strftime('%Y-%m-%d %H:%M')}  |  {self.title_text}"
            fm = QFontMetrics(wm_font)
            p.drawText(self.width - fm.horizontalAdvance(wm) - 20, self.height - 10, wm)
        p.end()
        return img

    def _draw_caret(self, p, x, y, h, char=" "):
        cw = max(2, self.fm.horizontalAdvance(char))
        ch = max(4, h - 2)
        if self.cursor_glow:
            gc = QColor(self._qc_cursor); gc.setAlpha(80)
            p.fillRect(x - 2, y - 1, cw + 4, ch + 2, gc)
            gc.setAlpha(140)
            p.fillRect(x - 1, y, cw + 2, ch, gc)
        p.fillRect(x, y, cw, ch, self._qc_cursor)
        if char != " " and char != "\t":
            p.setPen(QColor(self.theme["background"]))
            p.drawText(QRect(int(x), int(y), int(cw), int(ch)), Qt.AlignCenter, char)

# =====================================================================
# 9. MULTI-PANE RENDERER
# =====================================================================
class MultiPaneRenderer:
    def __init__(self, panes, frame_w, frame_h, num_panes=2,
                 orientation="landscape", gap=20, bg_color="#0d0d12"):
        self.panes = panes; self.frame_w = frame_w; self.frame_h = frame_h
        self.num_panes = max(1, min(num_panes, len(panes)))
        self.orientation = orientation; self.gap = gap; self.bg_color = bg_color
        self.pane_rects = self._compute_pane_rects()

    def _compute_pane_rects(self):
        W, H, g, n = self.frame_w, self.frame_h, self.gap, self.num_panes
        if n == 1: 
            return [QRect(0, 0, W, H)]
        if n == 2:
            if self.orientation == "landscape":
                pw = (W - g) // 2
                total_w = 2 * pw + g
                x_start = (W - total_w) // 2
                return [QRect(x_start, 0, pw, H), QRect(x_start + pw + g, 0, pw, H)]
            else:
                ph = (H - g) // 2
                total_h = 2 * ph + g
                y_start = (H - total_h) // 2
                return [QRect(0, y_start, W, ph), QRect(0, y_start + ph + g, W, ph)]
        pw = (W - g) // 2; ph = (H - g) // 2
        total_w = 2 * pw + g
        total_h = 2 * ph + g
        x_start = (W - total_w) // 2
        y_start = (H - total_h) // 2
        return [
            QRect(x_start, y_start, pw, ph), 
            QRect(x_start + pw + g, y_start, pw, ph),
            QRect(x_start, y_start + ph + g, pw, ph), 
            QRect(x_start + pw + g, y_start + ph + g, pw, ph)
        ]

    def duration(self):
        if not self.panes: return 0.0
        return max(anim.duration() for _, anim in self.panes)

    def char_timestamps_all(self):
        all_ts = []
        for _, anim in self.panes:
            all_ts.extend(anim.char_timestamps())
        return all_ts

    def compute_state(self, t):
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
                active_char = None; key_flash = 0.0
            vis_text = animator.text_snapshots[nv]
            vis_err = animator.error_snapshots[nv]
            states.append((vis_text, vis_err, cur_vis, active_char, round(key_flash, 2)))
        return tuple(states)

    def render_frame(self, t, target=None, precomputed_state=None):
        img = target if target is not None else QImage(self.frame_w, self.frame_h, QImage.Format_RGB32)
        img.fill(QColor(self.bg_color))
        p = QPainter(img)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        if precomputed_state is None:
            precomputed_state = self.compute_state(t)
        for i, ((renderer, animator), rect) in enumerate(zip(self.panes, self.pane_rects)):
            if i >= len(precomputed_state): break
            vis_text, vis_err, cur_vis, active_char, key_flash = precomputed_state[i]
            pane_img = renderer.render_frame(vis_text, vis_err, cur_vis,
                                             active_char=active_char, key_flash=key_flash)
            p.drawImage(rect.topLeft(), pane_img)
        if self.num_panes == 2:
            p.setPen(QPen(QColor(self.bg_color), max(4, self.gap // 2)))
            if self.orientation == "landscape":
                mid = self.pane_rects[0].right() + self.gap // 2
                p.drawLine(mid, 0, mid, self.frame_h)
            else:
                mid = self.pane_rects[0].bottom() + self.gap // 2
                p.drawLine(0, mid, self.frame_w, mid)
        p.end()
        return img

# =====================================================================
# 10. AUDIO WORKER & VIDEO EXPORTER
# =====================================================================
class AudioWorker(QObject):
    finished = Signal(object)
    error = Signal(str)

    def __init__(self, sound_params, timestamps, volume, filepath=None):
        super().__init__()
        self.sound_params = sound_params
        self.timestamps = timestamps
        self.volume = volume
        self.filepath = filepath

    @Slot()
    def run(self):
        try:
            preset, stereo, reverb_amt = self.sound_params
            sg = SimpleSoundGen(sr=44100, preset=preset, stereo=stereo, reverb_amt=reverb_amt)
            if self.filepath:
                sg.generate_track(self.timestamps, self.filepath, self.volume)
                self.finished.emit(self.filepath)
            else:
                pcm = sg.generate_pcm(self.timestamps, self.volume)
                if len(pcm) > 0:
                    ch = 2 if stereo else 1
                    wb = _pcm_to_wav_bytes(pcm, sg.sr, ch)
                    self.finished.emit(wb)
                else:
                    self.finished.emit(None)
        except Exception as e:
            log.error("Audio worker failed: %s", e, exc_info=True)
            self.error.emit(str(e))

def _format_eta(seconds):
    if seconds < 1: return "< 1s"
    if seconds < 60: return f"{int(seconds)}s"
    m, s = divmod(int(seconds), 60)
    if m < 60: return f"{m}m {s}s"
    h, m = divmod(m, 60)
    return f"{h}h {m}m {s}s"

class VideoExporter(QThread):
    progress = Signal(int)
    status = Signal(str)
    finished_ok = Signal(str)
    error = Signal(str)
    CHUNK_DURATION = 600.0

    def __init__(self, multi_pane, output, fps=30, sound_params=None, volume=0.5, encoder_name="YouTube Pro (H.264/AAC)"):
        super().__init__()
        self.multi_pane = multi_pane; self.output = output; self.fps = fps
        self.sound_params = sound_params
        self.volume = volume
        self.encoder_name = encoder_name
        self._cancel = threading.Event()

    def cancel(self): self._cancel.set()

    def _gen_chunk_audio(self, chunk_ts, chunk_aud):
        try:
            preset, stereo, reverb_amt = self.sound_params
            sg = SimpleSoundGen(sr=44100, preset=preset, stereo=stereo, reverb_amt=reverb_amt)
            sg.generate_track(chunk_ts, chunk_aud, self.volume)
            return os.path.getsize(chunk_aud) > 44
        except Exception as e:
            log.error("Audio chunk gen failed: %s", e)
            return False

    def run(self):
        tmp = ""
        try:
            os.makedirs(TEMP_DIR, exist_ok=True)
            tmp = tempfile.mkdtemp(dir=TEMP_DIR, prefix="export_")
            total_dur = self.multi_pane.duration()
            num_chunks = max(1, math.ceil(total_dur / self.CHUNK_DURATION))
            video_chunks = []
            audio_chunks = []
            audio_executor = ThreadPoolExecutor(max_workers=2) if self.sound_params else None
            audio_futures = {}
            for c_idx in range(num_chunks):
                if self._cancel.is_set(): break
                start_t = c_idx * self.CHUNK_DURATION
                end_t = min(total_dur, start_t + self.CHUNK_DURATION)
                start_frame = int(start_t * self.fps)
                n_chunk = int(end_t * self.fps) - start_frame
                self.status.emit(f"Rendering Chunk {c_idx+1}/{num_chunks}...")
                chunk_aud = os.path.join(tmp, f"aud_{c_idx}.wav")
                chunk_vid = os.path.join(tmp, f"vid_{c_idx}.mp4")
                if audio_executor:
                    all_ts = self.multi_pane.char_timestamps_all()
                    chunk_ts = [(ts - start_t, ch) for ts, ch in all_ts if start_t <= ts < end_t]
                    if chunk_ts:
                        audio_futures[c_idx] = audio_executor.submit(self._gen_chunk_audio, chunk_ts, chunk_aud)
                if not self._render_chunk_video(start_frame, n_chunk, chunk_vid):
                    raise RuntimeError(f"Failed to render video for chunk {c_idx+1}")
                video_chunks.append(chunk_vid)
                if c_idx in audio_futures and audio_futures[c_idx].result():
                    audio_chunks.append(chunk_aud)
                self.progress.emit(int(((c_idx + 1) / num_chunks) * 80))
            if self._cancel.is_set():
                self.error.emit("Cancelled"); return
            self.status.emit("Stitching video chunks...")
            final_video = os.path.join(tmp, "final_video.mp4")
            self._concat_files(video_chunks, final_video)
            if audio_chunks:
                self.status.emit("Stitching audio chunks...")
                final_audio = os.path.join(tmp, "final_audio.wav")
                self._concat_files(audio_chunks, final_audio)
                self.status.emit("Muxing final video and audio...")
                self._mux_final(final_video, final_audio, self.output)
            else:
                os.rename(final_video, self.output)
            self.progress.emit(100)
            self.status.emit(f"Done → {self.output}")
            self.finished_ok.emit(self.output)
        except Exception as e:
            log.error("Export failed: %s", e, exc_info=True)
            self.error.emit(str(e))
        finally:
            if tmp:
                try: shutil.rmtree(tmp, ignore_errors=True)
                except: pass

    def _concat_files(self, paths, out_path):
        concat_path = os.path.join(os.path.dirname(out_path), "concat_list.txt")
        with open(concat_path, "w", encoding="utf-8") as f:
            for p in paths:
                safe = p.replace("\\", "/").replace("'", r"\'")
                f.write(f"file '{safe}'\n")
        cmd = ["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", concat_path, "-c", "copy", out_path]
        si = None
        if platform.system() == "Windows":
            si = subprocess.STARTUPINFO()
            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, startupinfo=si)
        _, stderr = proc.communicate(timeout=120)
        if proc.returncode != 0:
            raise RuntimeError(f"Concat failed: {stderr.decode(errors='ignore')}")

    def _mux_final(self, vid_path, aud_path, out_path):
        cmd = ["ffmpeg", "-y", "-i", vid_path, "-i", aud_path,
               "-c:v", "copy", "-c:a", "aac", "-b:a", "256k", "-ar", "48000",
               "-movflags", "+faststart", out_path]
        si = None
        if platform.system() == "Windows":
            si = subprocess.STARTUPINFO()
            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, startupinfo=si)
        _, stderr = proc.communicate(timeout=120)
        if proc.returncode != 0:
            raise RuntimeError(f"Final mux failed: {stderr.decode(errors='ignore')}")

    def _render_chunk_video(self, start_frame, n_frames, out_path):
        w, h = self.multi_pane.frame_w, self.multi_pane.frame_h
        fps = self.fps
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
            bufsize = maxrate * 2
            cmd += ["-maxrate", f"{maxrate}", "-bufsize", f"{bufsize}"]
        if enc_cfg.get("color_tags", False):
            cmd += ["-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709"]
        cmd += ["-an", out_path]
        si = None
        if platform.system() == "Windows":
            si = subprocess.STARTUPINFO()
            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            si.wShowWindow = subprocess.SW_HIDE
        try:
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, startupinfo=si)
        except FileNotFoundError:
            self.error.emit("FFmpeg not found on PATH."); return False
        stderr_chunks = []
        def _drain():
            while True:
                chunk = proc.stderr.read(8192)
                if not chunk: break
                stderr_chunks.append(chunk)
        dt = threading.Thread(target=_drain, daemon=True); dt.start()
        scratch = QImage(w, h, QImage.Format_RGB32)
        wq = deque(); wl = threading.Lock(); wcv = threading.Condition(wl)
        we = []; wd = [False]
        def _writer():
            try:
                while True:
                    with wl:
                        while not wq and not wd[0]: wcv.wait(timeout=0.5)
                        if not wq and wd[0]: break
                        fd = wq.popleft()
                        if fd is None: break
                        try:
                            proc.stdin.write(fd)
                        except BrokenPipeError:
                            we.append("BrokenPipe")
                            break
            except Exception as ex: we.append(str(ex))
            finally:
                try: proc.stdin.close()
                except: pass
                wd[0] = True
                with wl: wcv.notify_all()
        wt = threading.Thread(target=_writer, daemon=True); wt.start()
        for fi in range(n_frames):
            if self._cancel.is_set() or we: break
            t = (start_frame + fi) / self.fps
            if fi % 100 == 0:
                self.status.emit(f"Rendering frame {fi}/{n_frames} ({_format_eta(t)})...")
            state = self.multi_pane.compute_state(t)
            qimg = self.multi_pane.render_frame(t, scratch, precomputed_state=state)
            
            # PySide6 constBits() returns a memoryview, safely convert to bytes
            img_bytes = bytes(qimg.constBits())
            
            with wl:
                while len(wq) >= 6: wcv.wait(timeout=0.1)
                if self._cancel.is_set() or we: break
                wq.append(img_bytes); wcv.notify_all()
        if not self._cancel.is_set() and not we:
            with wl: wq.append(None); wcv.notify_all()
        wt.join(timeout=600)
        if we: return False
        proc.wait(timeout=600); dt.join(timeout=5)
        if proc.returncode != 0:
            err = b"".join(stderr_chunks).decode(errors="ignore")[-600:]
            log.error("FFmpeg failed (code %d): %s", proc.returncode, err)
            return False
        return True

# =====================================================================
# 11. DEFAULT EXAMPLES
# =====================================================================
DEFAULT_TEMPLATES = [
    {
        "name": "Binary Search",
        "junior": '''def binary_search(arr, target):
    # This function does binary search
    # It searches for target in arr
    low = 0
    high = len(arr) - 1
    while low <= high:
        mid = (low + high) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            low = mid + 1
        else:
            high = mid - 1
    # If we get here, we didn't find it
    return -1

result = binary_search([1, 3, 5, 7, 9], 5)
print("Found at index:", result)
''',
        "senior": '''def binary_search(arr: list[int], target: int) -> int:
    """Return index of target in sorted arr, or -1 if absent."""
    lo, hi = 0, len(arr) - 1
    while lo <= hi:
        mid = (lo + hi) >> 1
        if arr[mid] == target:
            return mid
        lo, hi = (mid + 1, hi) if arr[mid] < target else (lo, mid - 1)
    return -1

print(binary_search([1, 3, 5, 7, 9], 5))
'''
    },
    {
        "name": "FizzBuzz",
        "junior": '''def fizzbuzz(n):
    result = []
    for i in range(1, n + 1):
        if i % 15 == 0:
            result.append("FizzBuzz")
        elif i % 3 == 0:
            result.append("Fizz")
        elif i % 5 == 0:
            result.append("Buzz")
        else:
            result.append(str(i))
    return result

print(fizzbuzz(15))
''',
        "senior": '''def fizzbuzz(n: int) -> list[str]:
    rules = {3: "Fizz", 5: "Buzz"}
    return [
        "".join(w for d, w in rules.items() if i % d == 0) or str(i)
        for i in range(1, n + 1)
    ]

print(fizzbuzz(15))
'''
    },
    {
        "name": "Fibonacci",
        "junior": '''def fibonacci(n):
    if n <= 1:
        return n
    return fibonacci(n - 1) + fibonacci(n - 2)

# Get the 10th fibonacci number
result = fibonacci(10)
print("Fibonacci of 10 is:", result)
''',
        "senior": '''from functools import lru_cache

@lru_cache(maxsize=None)
def fib(n: int) -> int:
    """Memoized Fibonacci - O(n) time, O(n) space."""
    return n if n < 2 else fib(n - 1) + fib(n - 2)

print(fib(100))
'''
    },
    {
        "name": "Flatten List",
        "junior": '''def flatten(lst):
    result = []
    for item in lst:
        if isinstance(item, list):
            for sub in flatten(item):
                result.append(sub)
        else:
            result.append(item)
    return result

print(flatten([1, [2, [3, 4]], 5]))
''',
        "senior": '''from collections.abc import Iterable

def flatten(items):
    for x in items:
        if isinstance(x, Iterable) and not isinstance(x, (str, bytes)):
            yield from flatten(x)
        else:
            yield x

print(list(flatten([1, [2, [3, 4]], 5])))
'''
    },
    {
        "name": "Group By",
        "junior": '''def group_by(items, key_func):
    groups = {}
    for item in items:
        key = key_func(item)
        if key not in groups:
            groups[key] = []
        groups[key].append(item)
    return groups

data = [1, 2, 3, 4, 5, 6]
result = group_by(data, lambda x: "even" if x % 2 == 0 else "odd")
print(result)
''',
        "senior": '''from itertools import groupby
from operator import itemgetter

def group_by(items, key_func):
    return {
        k: list(g) for k, g in
        groupby(sorted(items, key=key_func), key=key_func)
    }

data = [1, 2, 3, 4, 5, 6]
print(group_by(data, lambda x: "even" if x % 2 == 0 else "odd"))
'''
    },
]

def load_examples_from_disk(target_dir):
    if not os.path.exists(target_dir):
        os.makedirs(target_dir, exist_ok=True)
        for template in DEFAULT_TEMPLATES:
            safe_name = template["name"].replace(' ', '_').lower() + '.json'
            with open(os.path.join(target_dir, safe_name), 'w', encoding='utf-8') as f:
                json.dump(template, f, indent=4)
    examples = {}
    for filename in sorted(os.listdir(target_dir)):
        if not filename.endswith('.json'): continue
        try:
            with open(os.path.join(target_dir, filename), 'r', encoding='utf-8') as f:
                data = json.load(f)
            items = data if isinstance(data, list) else [data]
            for item in items:
                if not isinstance(item, dict): continue
                name = item.get("name", filename[:-5].replace('_', ' '))
                examples[name] = {
                    'junior': item.get("junior", "# Missing"),
                    'senior': item.get("senior", "# Missing")
                }
        except Exception as e:
            log.warning("Error loading %s: %s", filename, e)
    if not examples:
        examples['Empty'] = {'junior': f'# No examples in:\n# {target_dir}',
                             'senior': f'# No examples in:\n# {target_dir}'}
    return examples

# =====================================================================
# 12. PYTHON HIGHLIGHTER FOR UI
# =====================================================================
class PythonHighlighter(QSyntaxHighlighter):
    def __init__(self, document):
        super().__init__(document)
        self.rules = []
        keyword = QTextCharFormat()
        keyword.setForeground(QColor("#ff79c6"))
        keyword.setFontWeight(QFont.Bold)
        for word in ["def", "class", "return", "if", "else", "elif", "import", "from", "as", "for", "while", "try", "except", "finally", "with", "lambda", "yield", "pass", "break", "continue", "global", "nonlocal", "assert", "del", "in", "is", "not", "and", "or", "True", "False", "None"]:
            self.rules.append((QRegularExpression(rf"\b{word}\b"), keyword))
        string = QTextCharFormat()
        string.setForeground(QColor("#f1fa8c"))
        self.rules.append((QRegularExpression(r'".*?"'), string))
        self.rules.append((QRegularExpression(r"'.*?'"), string))
        self.rules.append((QRegularExpression(r'""".*?"""', QRegularExpression.DotMatchesEverythingOption), string))
        comment = QTextCharFormat()
        comment.setForeground(QColor("#6272a4"))
        comment.setFontItalic(True)
        self.rules.append((QRegularExpression(r"#[^\n]*"), comment))
        number = QTextCharFormat()
        number.setForeground(QColor("#bd93f9"))
        self.rules.append((QRegularExpression(r"\b\d+\.?\d*\b"), number))
        function = QTextCharFormat()
        function.setForeground(QColor("#50fa7b"))
        self.rules.append((QRegularExpression(r"\b[A-Za-z0-9_]+(?=\()"), function))

    def highlightBlock(self, text):
        for pattern, format in self.rules:
            it = pattern.globalMatch(text)
            while it.hasNext():
                match = it.next()
                self.setFormat(match.capturedStart(), match.capturedLength(), format)

# =====================================================================
# 13. MAIN WINDOW
# =====================================================================
_SAMPLE_CODE = _DEFAULT = DEFAULT_TEMPLATES[0]['junior']

class MainWindow(QMainWindow):
    KB_POS_MAP = {
        "Bottom Center": "bottom_center", "Bottom Right": "bottom_right",
        "Bottom Left": "bottom_left", "Center Left": "center_left",
        "Center Right": "center_right", "Top Center": "top_center",
        "Top Right": "top_right", "Top Left": "top_left",
    }

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Junior vs Senior Dev — Code Typing Studio")
        self.setMinimumSize(1100, 750)
        self.resize(1300, 850)
        self.examples = {}
        self.example_names = []
        self._examples_dir = INPUT_DIR
        self._exporter = None
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
        self._cached_key = None
        self._cached_mp = None
        self._cached_panes = []
        self._preview_scratch = None
        self._current_junior_code = ""
        self._current_senior_code = ""
        self._current_name = ""
        self._typing_seed = 42
        self._audio_workers = []
        self._shortcuts = []  # Prevent shortcuts from being garbage collected
        self._build_ui()
        self._connect_signals()
        self._load_settings()
        self._load_examples()
        QTimer.singleShot(300, self._update_preview)
        self._audio_player = QMediaPlayer(self)
        self._audio_out = QAudioOutput(self)
        self._audio_player.setAudioOutput(self._audio_out)
        self._audio_buf = None

    def _play_audio_bytes(self, data, vol):
        if self._audio_player:
            self._audio_player.stop()
            self._audio_player.setSource(QUrl())
            old_buf = self._audio_buf
            if old_buf:
                QTimer.singleShot(0, lambda: (old_buf.close(), old_buf.deleteLater()))
            self._audio_buf = QBuffer(self)
            self._audio_buf.setData(data)
            self._audio_buf.open(QIODevice.ReadOnly)
            self._audio_out.setVolume(vol)
            self._audio_player.setSourceDevice(self._audio_buf, QUrl())
            self._audio_player.play()

    def _build_ui(self):
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
        self.statusBar().showMessage("Ready — Load an example or paste custom code, then Play/Export")

    def _build_explorer(self, parent_layout):
        panel = QWidget()
        panel.setFixedWidth(260)
        pl = QVBoxLayout(panel)
        pl.setContentsMargins(0,0,0,0)
        pl.setSpacing(0)
        header = QFrame()
        header.setFixedHeight(40)
        header.setStyleSheet("QFrame { background-color: #1e1e2e; border-bottom: 1px solid #11111b; }")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(12, 0, 8, 0)
        title = QLabel("📋 INPUT EXAMPLES")
        title.setStyleSheet("color: #a6adc8; font-size: 11px; font-weight: bold; letter-spacing: 1px;")
        hl.addWidget(title)
        hl.addStretch()
        self.reload_btn = QPushButton("🔄")
        self.reload_btn.setFixedSize(24, 24)
        self.reload_btn.setCursor(Qt.PointingHandCursor)
        self.reload_btn.setStyleSheet("QPushButton { background: transparent; border: none; border-radius: 4px; } QPushButton:hover { background: #313244; }")
        self.reload_btn.clicked.connect(self._load_examples)
        hl.addWidget(self.reload_btn)
        self.folder_btn = QPushButton("📁")
        self.folder_btn.setFixedSize(24, 24)
        self.folder_btn.setCursor(Qt.PointingHandCursor)
        self.folder_btn.setStyleSheet("QPushButton { background: transparent; border: none; border-radius: 4px; } QPushButton:hover { background: #313244; }")
        self.folder_btn.clicked.connect(self._open_folder)
        hl.addWidget(self.folder_btn)
        pl.addWidget(header)
        self.search_bar = QLineEdit()
        self.search_bar.setPlaceholderText("Filter...")
        self.search_bar.setFixedHeight(30)
        self.search_bar.textChanged.connect(self._filter_examples)
        pl.addWidget(self.search_bar)
        self.example_list = QListView()
        self.example_list.setStyleSheet("QListView { background: #181825; border: none; outline: none; } QListView::item { padding: 6px 12px; border-bottom: 1px solid #11111b; } QListView::item:selected { background: #89b4fa; color: #1e1e2e; }")
        self.example_list.clicked.connect(self._on_example_clicked)
        self.example_model = QStandardItemModel()
        self.example_list.setModel(self.example_model)
        pl.addWidget(self.example_list, 1)
        parent_layout.addWidget(panel)

    def _build_header(self, parent_layout):
        header = QFrame()
        header.setFixedHeight(50)
        header.setStyleSheet("QFrame { background: #181825; border-bottom: 1px solid #11111b; }")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(20, 0, 20, 0)
        title = QLabel("⌨  Junior vs Senior Dev Studio")
        title.setStyleSheet("color: #cdd6f4; font-size: 16px; font-weight: bold;")
        hl.addWidget(title)
        self.path_label = QLabel("")
        self.path_label.setStyleSheet("color: #a6adc8; font-size: 11px;")
        hl.addWidget(self.path_label)
        hl.addStretch()
        hint = QLabel("Space: Play/Pause  ·  R: Reset  ·  Ctrl+E: Export")
        hint.setStyleSheet("color: #585b70; font-size: 10px;")
        hl.addWidget(hint)
        parent_layout.addWidget(header)

    def _build_preview_tab(self):
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
        shadow.setBlurRadius(20); shadow.setOffset(0, 4)
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
        self.frame_back_btn.setToolTip("Previous frame (←)")
        self.frame_back_btn.clicked.connect(lambda: self._seek_frame(-1))
        ctrl.addWidget(self.frame_back_btn)
        self.frame_slider = QSlider(Qt.Horizontal)
        self.frame_slider.setRange(0, 1000)
        self.frame_slider.setValue(0)
        self.frame_slider.valueChanged.connect(self._on_slider)
        ctrl.addWidget(self.frame_slider, 1)
        self.frame_fwd_btn = QPushButton("⏭")
        self.frame_fwd_btn.setFixedWidth(40)
        self.frame_fwd_btn.setToolTip("Next frame (→)")
        self.frame_fwd_btn.clicked.connect(lambda: self._seek_frame(1))
        ctrl.addWidget(self.frame_fwd_btn)
        self.loop_btn = QPushButton("🔁")
        self.loop_btn.setFixedWidth(40)
        self.loop_btn.setCheckable(True)
        self.loop_btn.setToolTip("Loop (L)")
        self.loop_btn.toggled.connect(self._toggle_loop)
        ctrl.addWidget(self.loop_btn)
        self.play_btn = QPushButton("▶ Animate")
        self.play_btn.setFixedWidth(110)
        self.play_btn.setStyleSheet("QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 6px; } QPushButton:hover { background: #94e2d5; }")
        self.play_btn.clicked.connect(self._toggle_preview_anim)
        ctrl.addWidget(self.play_btn)
        self.fullscreen_btn = QPushButton("⛶")
        self.fullscreen_btn.setFixedWidth(40)
        self.fullscreen_btn.setToolTip("Fullscreen (F)")
        self.fullscreen_btn.clicked.connect(self._toggle_fullscreen)
        ctrl.addWidget(self.fullscreen_btn)
        layout.addLayout(ctrl)
        help_label = QLabel("Space: Play/Pause  ·  ←/→: Seek frame  ·  Shift+←/→: Seek 5s  ·  L: Loop  ·  F: Fullscreen  ·  R: Reset")
        help_label.setStyleSheet("color: #585b70; font-size: 10px;")
        help_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(help_label)
        self.tabs.addTab(tab, "🎬 Preview & Export")

    def _build_settings_tab(self):
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
        self.font_family_cb = QComboBox()
        _mono = ["Consolas", "JetBrains Mono", "Fira Code", "Cascadia Code",
                 "Source Code Pro", "Inconsolata", "DejaVu Sans Mono", "monospace"]
        _avail = QFontDatabase.families()
        for f in sorted(_avail):
            if f not in _mono: _mono.append(f)
        self.font_family_cb.addItems([f for f in _mono if f in _avail or f == "monospace"])
        self.font_family_cb.setCurrentText("Consolas" if "Consolas" in _avail else "monospace")
        fl.addRow("Code Font:", self.font_family_cb)
        self.font_size_auto = QCheckBox("Auto")
        self.font_size_auto.setChecked(True)
        self.font_size_sp = QSpinBox()
        self.font_size_sp.setRange(8, 72)
        self.font_size_sp.setValue(18)
        self.font_size_sp.setEnabled(False)
        self.font_size_auto.toggled.connect(self.font_size_sp.setEnabled)
        fs_row = QHBoxLayout(); fs_row.addWidget(self.font_size_auto); fs_row.addWidget(self.font_size_sp)
        fl.addRow("Font Size:", fs_row)
        self.lang_cb = QComboBox()
        self.lang_cb.addItems(["Auto", "Python", "JavaScript", "TypeScript", "CFamily", "Go", "Rust"])
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
        j_grp = QGroupBox("Junior Dev")
        j_grp.setStyleSheet("QGroupBox { color: #89b4fa; font-weight: bold; }")
        j_fl = QFormLayout(j_grp)
        self.j_wpm = QSpinBox(); self.j_wpm.setRange(30, 300); self.j_wpm.setValue(90)
        j_fl.addRow("WPM:", self.j_wpm)
        self.j_typo = QDoubleSpinBox(); self.j_typo.setRange(0, 0.2); self.j_typo.setSingleStep(0.005); self.j_typo.setDecimals(3); self.j_typo.setValue(0.028)
        j_fl.addRow("Typo Rate:", self.j_typo)
        self.j_pause = QDoubleSpinBox(); self.j_pause.setRange(0, 1); self.j_pause.setSingleStep(0.05); self.j_pause.setValue(0.15)
        j_fl.addRow("Pause Freq:", self.j_pause)
        self.j_burst = QDoubleSpinBox(); self.j_burst.setRange(0, 1); self.j_burst.setSingleStep(0.05); self.j_burst.setValue(0.15)
        j_fl.addRow("Burst Chance:", self.j_burst)
        devs_row.addWidget(j_grp)
        s_grp = QGroupBox("Senior Dev")
        s_grp.setStyleSheet("QGroupBox { color: #a6e3a1; font-weight: bold; }")
        s_fl = QFormLayout(s_grp)
        self.s_wpm = QSpinBox(); self.s_wpm.setRange(30, 300); self.s_wpm.setValue(130)
        s_fl.addRow("WPM:", self.s_wpm)
        self.s_typo = QDoubleSpinBox(); self.s_typo.setRange(0, 0.2); self.s_typo.setSingleStep(0.005); self.s_typo.setDecimals(3); self.s_typo.setValue(0.005)
        s_fl.addRow("Typo Rate:", self.s_typo)
        self.s_pause = QDoubleSpinBox(); self.s_pause.setRange(0, 1); self.s_pause.setSingleStep(0.05); self.s_pause.setValue(0.05)
        s_fl.addRow("Pause Freq:", self.s_pause)
        self.s_burst = QDoubleSpinBox(); self.s_burst.setRange(0, 1); self.s_burst.setSingleStep(0.05); self.s_burst.setValue(0.35)
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
        self.res_cb = QComboBox()
        self._populate_resolutions()
        el.addRow("Resolution:", self.res_cb)
        self.fps_sp = QSpinBox(); self.fps_sp.setRange(10, 60); self.fps_sp.setValue(30)
        el.addRow("FPS:", self.fps_sp)
        self.encoder_cb = QComboBox()
        self.encoder_cb.addItems(list(ENCODERS.keys()))
        el.addRow("Encoder:", self.encoder_cb)
        self.start_pause_sp = QDoubleSpinBox(); self.start_pause_sp.setRange(0, 10); self.start_pause_sp.setSingleStep(0.5); self.start_pause_sp.setValue(0.5)
        el.addRow("Start Pause (s):", self.start_pause_sp)
        self.end_pause_sp = QDoubleSpinBox(); self.end_pause_sp.setRange(0, 10); self.end_pause_sp.setSingleStep(0.5); self.end_pause_sp.setValue(1.5)
        el.addRow("End Pause (s):", self.end_pause_sp)
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
        self.reverb_sp = QDoubleSpinBox(); self.reverb_sp.setRange(0, 0.5); self.reverb_sp.setSingleStep(0.05); self.reverb_sp.setValue(0.10)
        al.addRow("ASMR Reverb:", self.reverb_sp)
        self.vol_sp = QSpinBox(); self.vol_sp.setRange(0, 100); self.vol_sp.setValue(50); self.vol_sp.setSuffix("%")
        al.addRow("Volume:", self.vol_sp)
        test_row = QHBoxLayout()
        self.test_btn = QPushButton("🔊 Test Sound")
        self.test_btn.clicked.connect(self._test_sound)
        test_row.addWidget(self.test_btn); test_row.addStretch()
        al.addRow(test_row)
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
        self.kb_opacity = QDoubleSpinBox(); self.kb_opacity.setRange(0.1, 1.0); self.kb_opacity.setSingleStep(0.05); self.kb_opacity.setValue(0.82)
        kl.addRow("Opacity:", self.kb_opacity)
        cl.addWidget(kb_grp)
        custom_grp = QGroupBox("Custom Code Input")
        cul = QVBoxLayout(custom_grp)
        j_row = QHBoxLayout()
        j_row.addWidget(QLabel("Junior Dev:"))
        j_copy_btn = QPushButton("📋 Copy")
        j_copy_btn.clicked.connect(lambda: self._copy_code('j'))
        j_row.addWidget(j_copy_btn)
        cul.addLayout(j_row)
        self.custom_junior = QPlainTextEdit()
        self.custom_junior.setPlaceholderText("Paste Junior Dev code here...")
        self.custom_junior.setMaximumHeight(120)
        self.custom_junior.setStyleSheet("QPlainTextEdit { background: #11111b; color: #cdd6f4; font-family: monospace; font-size: 11px; border: 1px solid #89b4fa; border-radius: 4px; }")
        cul.addWidget(self.custom_junior)
        s_row = QHBoxLayout()
        s_row.addWidget(QLabel("Senior Dev:"))
        s_copy_btn = QPushButton("📋 Copy")
        s_copy_btn.clicked.connect(lambda: self._copy_code('s'))
        s_row.addWidget(s_copy_btn)
        cul.addLayout(s_row)
        self.custom_senior = QPlainTextEdit()
        self.custom_senior.setPlaceholderText("Paste Senior Dev code here...")
        self.custom_senior.setMaximumHeight(120)
        self.custom_senior.setStyleSheet("QPlainTextEdit { background: #11111b; color: #cdd6f4; font-family: monospace; font-size: 11px; border: 1px solid #a6e3a1; border-radius: 4px; }")
        cul.addWidget(self.custom_senior)
        self.load_custom_btn = QPushButton("Load Custom Code")
        self.load_custom_btn.clicked.connect(self._load_custom)
        cul.addWidget(self.load_custom_btn)
        cl.addWidget(custom_grp)
        cl.addStretch()
        scroll.setWidget(container)
        self.tabs.addTab(scroll, "⚙ Settings")
        self.j_highlighter = PythonHighlighter(self.custom_junior.document())
        self.s_highlighter = PythonHighlighter(self.custom_senior.document())

    def _build_controls(self, parent_layout):
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
        self.randomize_btn = QPushButton("🎲 Randomize Typing")
        self.randomize_btn.setCursor(Qt.PointingHandCursor)
        self.randomize_btn.setStyleSheet("QPushButton { background: #45475a; color: #cdd6f4; border: none; border-radius: 6px; padding: 0 12px; } QPushButton:hover { background: #585b70; }")
        self.randomize_btn.clicked.connect(self._randomize_seed)
        bl.addWidget(self.randomize_btn)
        bl.addStretch()
        self.progress_bar = QProgressBar()
        self.progress_bar.setFixedWidth(200)
        self.progress_bar.setVisible(False)
        bl.addWidget(self.progress_bar)
        self.export_audio_btn = QPushButton("🎵 Export Audio")
        self.export_audio_btn.setFixedHeight(36)
        self.export_audio_btn.setCursor(Qt.PointingHandCursor)
        self.export_audio_btn.setStyleSheet("QPushButton { background: #cba6f7; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 0 16px; } QPushButton:hover { background: #b4befe; }")
        self.export_audio_btn.clicked.connect(self._start_audio_export)
        bl.addWidget(self.export_audio_btn)
        self.export_btn = QPushButton("🎬 Export Video")
        self.export_btn.setFixedHeight(36)
        self.export_btn.setCursor(Qt.PointingHandCursor)
        self.export_btn.setStyleSheet("QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 0 16px; } QPushButton:hover { background: #94e2d5; }")
        self.export_btn.clicked.connect(self._start_export)
        bl.addWidget(self.export_btn)
        parent_layout.addWidget(bar)

    def _populate_resolutions(self):
        fmt = self.export_format_cb.currentText()
        self.res_cb.clear()
        for res in EXPORT_FORMATS.get(fmt, EXPORT_FORMATS["YouTube (16:9)"])["resolutions"]:
            self.res_cb.addItem(res)

    def _apply_quality_preset(self, preset_name):
        if not hasattr(self, 'export_format_cb'): return
        preset = QUALITY_PRESETS.get(preset_name)
        if not preset: return
        fmt = self.export_format_cb.currentText()
        if preset['res'] in EXPORT_FORMATS.get(fmt, {}).get('resolutions', {}):
            idx = self.res_cb.findText(preset['res'])
            if idx >= 0: self.res_cb.setCurrentIndex(idx)
        self.fps_sp.setValue(preset['fps'])
        idx = self.encoder_cb.findText(preset['encoder'])
        if idx >= 0: self.encoder_cb.setCurrentIndex(idx)

    def _connect_signals(self):
        self.export_format_cb.currentTextChanged.connect(self._populate_resolutions)
        self.sound_preset_cb.currentTextChanged.connect(
            lambda t: self.preset_desc.setText(SOUND_PRESETS.get(t, {}).get("desc", "")))
        
        for w in [self.theme_cb, self.font_family_cb, self.font_size_sp, self.chrome_chk,
                  self.line_nums_chk, self.cursor_glow_chk, self.watermark_chk,
                  self.export_format_cb, self.res_cb, self.fps_sp, self.encoder_cb,
                  self.start_pause_sp, self.end_pause_sp,
                  self.j_wpm, self.j_typo, self.j_pause, self.j_burst,
                  self.s_wpm, self.s_typo, self.s_pause, self.s_burst,
                  self.sound_chk, self.sound_preset_cb, self.binaural_chk,
                  self.reverb_sp, self.vol_sp,
                  self.kb_chk, self.kb_layout_cb, self.kb_pos_cb, self.kb_opacity,
                  self.font_size_auto, self.bg_edit, self.lang_cb]:
            if hasattr(w, 'currentTextChanged'):
                w.currentTextChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'valueChanged'):
                w.valueChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'stateChanged'):
                w.stateChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'textChanged'):
                w.textChanged.connect(self._invalidate_and_schedule)
            if hasattr(w, 'toggled'):
                w.toggled.connect(self._invalidate_and_schedule)

        # PySide6 QShortcut binding fix
        def _bind(key, cb):
            s = QShortcut(QKeySequence(key), self)
            s.activated.connect(cb)
            self._shortcuts.append(s)

        _bind(Qt.Key_Space, self._toggle_preview_anim)
        _bind("R", self._reset_preview)
        _bind("Ctrl+E", self._start_export)
        _bind(Qt.Key_Left, lambda: self._seek_frame(-1))
        _bind(Qt.Key_Right, lambda: self._seek_frame(1))
        _bind("Shift+Left", lambda: self._seek_preview(-5))
        _bind("Shift+Right", lambda: self._seek_preview(5))
        _bind("L", lambda: (self.loop_btn.toggle(), self._toggle_loop(self.loop_btn.isChecked())))
        _bind("F", self._toggle_fullscreen)
        _bind(Qt.Key_Home, self._seek_start)
        _bind(Qt.Key_End, self._seek_end)

    def _seek_start(self):
        self._stop_preview_anim()
        self._preview_progress = 0.0
        self._update_preview()

    def _seek_end(self):
        self._stop_preview_anim()
        self._preview_progress = 1.0
        self._update_preview()

    def _invalidate_and_schedule(self, *_):
        if self._loading_settings: return
        self._cached_key = None; self._cached_mp = None; self._cached_panes = []
        self._preview_scratch = None
        if not hasattr(self, '_sched_timer'):
            self._sched_timer = QTimer(self)
            self._sched_timer.setSingleShot(True)
            self._sched_timer.setInterval(300)
            self._sched_timer.timeout.connect(self._update_preview)
        self._sched_timer.start()

    def _load_examples(self):
        self.examples = load_examples_from_disk(self._examples_dir)
        self.example_names = list(self.examples.keys())
        self.example_model.clear()
        for name in self.example_names:
            item = QStandardItem(name)
            item.setEditable(False)
            self.example_model.appendRow(item)
        self.path_label.setText(f"📂 {self._examples_dir} ({len(self.example_names)} files)")
        if self.example_names:
            self._on_example_clicked(self.example_model.index(0, 0))

    def _open_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Examples Folder", self._examples_dir)
        if folder:
            self._examples_dir = folder
            self._load_examples()

    def _filter_examples(self, text):
        text = text.lower()
        for i in range(self.example_model.rowCount()):
            item = self.example_model.item(i)
            item.setVisible(text in item.text().lower())

    def _on_example_clicked(self, index):
        if not index.isValid(): return
        name = self.example_model.itemFromIndex(index).text()
        if name not in self.examples: return
        ex = self.examples[name]
        self._current_junior_code = ex['junior']
        self._current_senior_code = ex['senior']
        self._current_name = name
        self.custom_junior.setPlainText(ex['junior'])
        self.custom_senior.setPlainText(ex['senior'])
        self._invalidate_and_schedule()
        self.statusBar().showMessage(f"Loaded: {name}")

    def _load_custom(self):
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

    def _copy_code(self, dev_type):
        if dev_type == 'j':
            text = self.custom_junior.toPlainText()
        else:
            text = self.custom_senior.toPlainText()
        if text:
            QApplication.clipboard().setText(text)
            self.statusBar().showMessage("Code copied to clipboard!", 2000)

    def _browse_bg(self):
        path, _ = QFileDialog.getOpenFileName(self, "Background Image", "", "Images (*.png *.jpg *.jpeg *.bmp)")
        if path:
            self._bg_image_path = path
            self.bg_edit.setText(path)

    def _start_audio_worker(self, timestamps, volume, filepath=None, callback=None):
        sound_params = (
            self.sound_preset_cb.currentText(),
            self.binaural_chk.isChecked(),
            self.reverb_sp.value()
        )
        worker = AudioWorker(sound_params, timestamps, volume, filepath)
        thread = QThread()
        worker.moveToThread(thread)
        thread.started.connect(worker.run)
        if callback:
            worker.finished.connect(callback)
        worker.error.connect(lambda e: QMessageBox.warning(self, "Audio Error", e))
        worker.finished.connect(thread.quit)
        worker.error.connect(thread.quit)
        thread.finished.connect(worker.deleteLater)
        thread.finished.connect(thread.deleteLater)
        thread.finished.connect(lambda t=thread: self._audio_workers.remove(t) if t in self._audio_workers else None)
        self._audio_workers.append(thread)
        thread.start()

    def _test_sound(self):
        vol = self.vol_sp.value() / 100.0
        ts = []; t = 0.0
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
        self._start_audio_worker(ts, vol, callback=on_finished)

    def _build_panes(self):
        fmt = self.export_format_cb.currentText()
        fmt_data = EXPORT_FORMATS.get(fmt, EXPORT_FORMATS["YouTube (16:9)"])
        orientation = fmt_data["orientation"]
        res_name = self.res_cb.currentText()
        w, h = fmt_data["resolutions"].get(res_name, (1920, 1080))
        theme_name = self.theme_cb.currentText()
        theme = THEMES[theme_name]
        pad = 24; chrome = self.chrome_chk.isChecked()
        ln = self.line_nums_chk.isChecked()
        font_family = self.font_family_cb.currentText()
        show_kb = self.kb_chk.isChecked()
        kb_layout = self.kb_layout_cb.currentText()
        kb_pos = self.KB_POS_MAP.get(self.kb_pos_cb.currentText(), "bottom_center")
        kb_op = self.kb_opacity.value()
        junior_code = self._current_junior_code or _SAMPLE_CODE
        senior_code = self._current_senior_code or _SAMPLE_CODE
        jp = TypingProfile(
            name="Junior Dev", wpm=self.j_wpm.value(), typo_rate=self.j_typo.value(),
            pause_freq=self.j_pause.value(), burst_chance=self.j_burst.value(),
            start_pause=self.start_pause_sp.value(), end_pause=self.end_pause_sp.value(),
        )
        sp = TypingProfile(
            name="Senior Dev", wpm=self.s_wpm.value(), typo_rate=self.s_typo.value(),
            pause_freq=self.s_pause.value(), burst_chance=self.s_burst.value(),
            start_pause=self.start_pause_sp.value(), end_pause=self.end_pause_sp.value(),
        )
        gap = 20
        if orientation == "landscape":
            pw = (w - gap) // 2; ph = h
        else:
            pw = w; ph = (h - gap) // 2
        panes = []
        for i, (code, profile, title, accent_key) in enumerate([
            (junior_code, jp, f"👶 Junior Dev — {self._current_name}", "junior_accent"),
            (senior_code, sp, f"🧓 Senior Dev — {self._current_name}", "senior_accent"),
        ]):
            lang_text = self.lang_cb.currentText()
            if lang_text == "Auto":
                stripped = code.lstrip()
                if stripped.startswith("<?php"): language = "Python"
                elif "func " in code or "package main" in code: language = "Go"
                elif "fn " in code or "impl " in code: language = "Rust"
                elif "function " in code or "const " in code or "var " in code: language = "JavaScript"
                elif "#include" in code or "std::" in code: language = "CFamily"
                else: language = "Python"
            else:
                language = lang_text
            code_lines = code.count("\n") + 1
            kb_overlay = None; kb_h = 0
            if show_kb:
                kb_overlay = KeyboardOverlay(
                    video_w=pw, video_h=ph, layout_name=kb_layout,
                    theme=theme, max_height=(ph - 2 * pad) // 3,
                    position=kb_pos, opacity=kb_op,
                )
                kb_h = kb_overlay.height_needed()
            if self.font_size_auto.isChecked():
                font_size = CodeRenderer.auto_font_size(
                    code_lines=code_lines, width=pw, height=ph, code=code,
                    font_family=font_family, keyboard_h=kb_h,
                    padding=pad, show_chrome=chrome, show_ln=ln,
                )
            else:
                font_size = max(8, int(self.font_size_sp.value() * 0.65))
            renderer = CodeRenderer(
                width=pw, height=ph, theme_name=theme_name,
                font_family=font_family, font_size=font_size,
                title_text=title, language=language,
                keyboard_overlay=kb_overlay, padding=pad,
                show_window_chrome=chrome, show_line_numbers=ln,
                bg_image_path=self._bg_image_path if i == 0 else None,
                total_code_lines=code_lines,
                cursor_glow=self.cursor_glow_chk.isChecked(),
                show_watermark=self.watermark_chk.isChecked() and i == 0,
                accent_color=theme.get(accent_key, "#7aa2f7"),
            )
            renderer.set_full_code(code)
            animator = TypingAnimator(code, profile, seed=i * 1000 + self._typing_seed)
            panes.append((renderer, animator))
        mp = MultiPaneRenderer(panes=panes, frame_w=w, frame_h=h,
                               num_panes=2, orientation=orientation, gap=gap)
        return mp

    def _get_multi_pane(self):
        key = (
            self.export_format_cb.currentText(), self.res_cb.currentText(),
            self.theme_cb.currentText(), self.font_family_cb.currentText(),
            self.font_size_auto.isChecked(), self.font_size_sp.value(),
            self.chrome_chk.isChecked(), self.line_nums_chk.isChecked(),
            self.cursor_glow_chk.isChecked(), self.watermark_chk.isChecked(),
            self._bg_image_path, self.kb_chk.isChecked(),
            self.kb_layout_cb.currentText(), self.kb_pos_cb.currentText(),
            self.kb_opacity.value(),
            self.j_wpm.value(), self.j_typo.value(), self.j_pause.value(), self.j_burst.value(),
            self.s_wpm.value(), self.s_typo.value(), self.s_pause.value(), self.s_burst.value(),
            self.start_pause_sp.value(), self.end_pause_sp.value(),
            self._current_junior_code, self._current_senior_code,
            self._typing_seed, self.lang_cb.currentText()
        )
        if key != self._cached_key:
            self._cached_key = key
            self._cached_mp = self._build_panes()
            self._preview_scratch = QImage(self._cached_mp.frame_w, self._cached_mp.frame_h, QImage.Format_RGB32)
        return self._cached_mp

    def _update_preview(self):
        try:
            mp = self._get_multi_pane()
            if mp is None or not mp.panes: return
            total_dur = mp.duration()
            t = total_dur * self._preview_progress
            state = mp.compute_state(t)
            qimg = mp.render_frame(t, self._preview_scratch, precomputed_state=state)
            scaled = QPixmap.fromImage(qimg).scaled(
                self.preview_label.size(), Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation)
            self.preview_label.setPixmap(scaled)
            cur_m, cur_s = divmod(int(t), 60)
            tot_m, tot_s = divmod(int(total_dur), 60)
            self.time_label.setText(f"{cur_m}:{cur_s:02d} / {tot_m}:{tot_s:02d}")
            self.pct_label.setText(f"{int(self._preview_progress * 100)}%")
            total_visible = sum(len(s[0]) for s in state)
            total_chars = sum(len(a.text_snapshots[-1]) for _, a in mp.panes)
            total_typos = sum(a.typo_count for _, a in mp.panes)
            elapsed_min = max(t / 60.0, 0.001)
            wpm = int((total_visible / 5) / elapsed_min) if t > 0.3 else 0
            self.stats_label.setText(
                f"  |  WPM: {wpm}  |  Chars: {total_visible}/{total_chars}  |  Typos: {total_typos}"
            )
            self.info_label.setText(f"{mp.frame_w}×{mp.frame_h}  |  2 panes  |  Font: {mp.panes[0][0].font_family} {mp.panes[0][0].font_size}px  |  {total_visible}/{total_chars} chars")
            self.duration_label.setText(f"Duration: {_format_eta(total_dur)}")
            self.frame_slider.blockSignals(True)
            self.frame_slider.setValue(int(self._preview_progress * 1000))
            self.frame_slider.blockSignals(False)
        except Exception as e:
            log.warning("Preview failed: %s", e, exc_info=True)

    def _on_slider(self, value):
        self._stop_preview_anim()
        self._preview_progress = value / 1000.0
        self._update_preview()

    def _seek_preview(self, delta):
        self._stop_preview_anim()
        mp = self._get_multi_pane()
        if mp is None: return
        total = mp.duration()
        self._preview_anim_t = max(0, min(total, total * self._preview_progress + delta))
        self._preview_progress = max(0, min(1.0, self._preview_anim_t / total)) if total > 0 else 0
        self._update_preview()

    def _seek_frame(self, direction):
        self._stop_preview_anim()
        mp = self._get_multi_pane()
        if mp is None: return
        fps = self.fps_sp.value()
        delta = direction / fps
        total = mp.duration()
        self._preview_anim_t = max(0, min(total, total * self._preview_progress + delta))
        self._preview_progress = self._preview_anim_t / total if total > 0 else 0
        self._update_preview()

    def _toggle_loop(self, checked):
        self._preview_loop = checked
        self.statusBar().showMessage(f"Loop {'enabled' if checked else 'disabled'}", 1500)

    def _toggle_fullscreen(self):
        if self.preview_label.isFullScreen():
            self.preview_label.showNormal()
            self.preview_label.setParent(self._preview_parent_container)
        else:
            self._preview_parent_container = self.preview_label.parentWidget()
            self.preview_label.setParent(None)
            self.preview_label.showFullScreen()
            self._update_preview()

    def _on_preview_click(self, event):
        self._toggle_preview_anim()

    def _toggle_preview_anim(self):
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
                def on_audio_ready(data):
                    if data and isinstance(data, bytes) and self._preview_animating:
                        self._play_audio_bytes(data, vol)
                self._start_audio_worker(ts, vol, callback=on_audio_ready)
            self._preview_timer.start()

    def _advance_preview(self):
        dt = self._preview_clock.restart() / 1000.0
        dt = min(dt, 0.1)
        self._preview_anim_t += dt
        mp = self._get_multi_pane()
        if mp is None:
            self._stop_preview_anim(); return
        total = mp.duration()
        if self._preview_anim_t >= total:
            if self._preview_loop:
                self._preview_anim_t = 0.0
            else:
                self._preview_anim_t = total
                self._stop_preview_anim()
        self._preview_progress = min(1.0, self._preview_anim_t / total) if total > 0 else 0.0
        self._update_preview()

    def _stop_preview_anim(self):
        self._preview_animating = False
        self._preview_timer.stop()
        self.play_btn.setText("▶ Animate")
        self.play_pause_btn.setText("▶ Play")
        if self._audio_player:
            self._audio_player.stop()
            self._audio_player.setSource(QUrl())
        if self._audio_buf:
            old_buf = self._audio_buf
            self._audio_buf = None
            QTimer.singleShot(0, lambda: (old_buf.close(), old_buf.deleteLater()))

    def _reset_preview(self):
        self._stop_preview_anim()
        self._preview_progress = 0.0
        self._preview_anim_t = 0.0
        self._update_preview()
        self.statusBar().showMessage("Reset to start")

    def _randomize_seed(self):
        self._typing_seed = random.randint(1, 99999)
        self._invalidate_and_schedule()
        self.statusBar().showMessage(f"Typing randomized (Seed: {self._typing_seed})")

    def _start_export(self):
        if shutil.which("ffmpeg") is None:
            QMessageBox.critical(self, "FFmpeg Not Found",
                                 "FFmpeg is not installed or not on PATH.\nPlease install FFmpeg.")
            return
        if not self._current_junior_code or not self._current_senior_code:
            QMessageBox.information(self, "No Code", "Please load an example or custom code first.")
            return
        self._stop_preview_anim()
        mp = self._get_multi_pane()
        if mp is None: return
        fmt = self.export_format_cb.currentText()
        suffix = "_shorts" if "Shorts" in fmt else "_youtube"
        base = self._current_name.replace(' ', '_').lower() if self._current_name else "comparison"
        default_name = f"{base}{suffix}.mp4"
        default_dir = QStandardPaths.writableLocation(QStandardPaths.DocumentsLocation)
        default_path = os.path.join(default_dir, default_name)
        path, _ = QFileDialog.getSaveFileName(self, "Export Video", default_path, "MP4 Video (*.mp4)")
        if not path: return
        if not path.lower().endswith('.mp4'): path += '.mp4'
        sound_params = None
        if self.sound_chk.isChecked():
            sound_params = (
                self.sound_preset_cb.currentText(),
                self.binaural_chk.isChecked(),
                self.reverb_sp.value()
            )
        self.progress_bar.setVisible(True)
        self.progress_bar.setValue(0)
        self.export_btn.setEnabled(False)
        self.export_btn.setText("⏸ Cancel")
        try:
            self.export_btn.clicked.disconnect()
            self.export_btn.clicked.connect(self._cancel_export)
        except: pass
        self._exporter = VideoExporter(
            multi_pane=mp,
            output=path,
            fps=self.fps_sp.value(),
            sound_params=sound_params,
            volume=self.vol_sp.value() / 100.0,
            encoder_name=self.encoder_cb.currentText(),
        )
        self._exporter.progress.connect(self._on_export_progress)
        self._exporter.status.connect(self.statusBar().showMessage)
        self._exporter.finished_ok.connect(lambda p: self._on_export_done(p))
        self._exporter.error.connect(lambda e: self._on_export_error(e))
        self._exporter.start()
        self.statusBar().showMessage("Exporting video...")

    def _cancel_export(self):
        if self._exporter:
            self._exporter.cancel()
            self.statusBar().showMessage("Cancelling export...")

    def _on_export_progress(self, val):
        self.progress_bar.setValue(val)
        self.setWindowTitle(f"[Exporting {val}%] Junior vs Senior Dev — Code Typing Studio")

    def _on_export_done(self, path):
        self.progress_bar.setVisible(False)
        self.export_btn.setEnabled(True)
        self.export_btn.setText("🎬 Export Video")
        self.setWindowTitle("Junior vs Senior Dev — Code Typing Studio")
        try:
            self.export_btn.clicked.disconnect()
            self.export_btn.clicked.connect(self._start_export)
        except: pass
        self._exporter = None
        self.statusBar().showMessage(f"Export complete! → {path}", 5000)
        QMessageBox.information(self, "Export Complete", f"Video saved to:\n{path}")

    def _on_export_error(self, err):
        self.progress_bar.setVisible(False)
        self.export_btn.setEnabled(True)
        self.export_btn.setText("🎬 Export Video")
        self.setWindowTitle("Junior vs Senior Dev — Code Typing Studio")
        try:
            self.export_btn.clicked.disconnect()
            self.export_btn.clicked.connect(self._start_export)
        except: pass
        self._exporter = None
        self.statusBar().showMessage("Export failed.", 5000)
        QMessageBox.warning(self, "Export Failed", err)

    def _start_audio_export(self):
        if not self._current_junior_code or not self._current_senior_code:
            QMessageBox.information(self, "No Code", "Please load an example or custom code first.")
            return
        base = self._current_name.replace(' ', '_').lower() if self._current_name else "comparison"
        default_dir = QStandardPaths.writableLocation(QStandardPaths.DocumentsLocation)
        default_path = os.path.join(default_dir, f"{base}_audio.wav")
        path, _ = QFileDialog.getSaveFileName(self, "Export Audio", default_path, "WAV Audio (*.wav)")
        if not path: return
        if not path.lower().endswith('.wav'): path += '.wav'
        mp = self._get_multi_pane()
        if mp is None: return
        self.statusBar().showMessage("Generating audio in background...")
        self.export_audio_btn.setEnabled(False)
        self.export_audio_btn.setText("⏳ Generating...")
        vol = self.vol_sp.value() / 100.0
        ts = mp.char_timestamps_all()
        def on_finished(filepath):
            self.export_audio_btn.setEnabled(True)
            self.export_audio_btn.setText("🎵 Export Audio")
            if filepath:
                self.statusBar().showMessage(f"Audio exported! → {filepath}", 5000)
                QMessageBox.information(self, "Export Complete", f"Audio saved to:\n{filepath}")
            else:
                self.statusBar().showMessage("Audio export failed.", 5000)
        self._start_audio_worker(ts, vol, filepath=path, callback=on_finished)

    def _save_settings(self):
        try:
            data = {
                "theme": self.theme_cb.currentText(),
                "font_family": self.font_family_cb.currentText(),
                "font_size_auto": self.font_size_auto.isChecked(),
                "font_size": self.font_size_sp.value(),
                "show_chrome": self.chrome_chk.isChecked(),
                "show_line_numbers": self.line_nums_chk.isChecked(),
                "cursor_glow": self.cursor_glow_chk.isChecked(),
                "watermark": self.watermark_chk.isChecked(),
                "bg_image_path": self._bg_image_path,
                "export_format": self.export_format_cb.currentText(),
                "resolution": self.res_cb.currentText(),
                "fps": self.fps_sp.value(),
                "encoder": self.encoder_cb.currentText(),
                "start_pause": self.start_pause_sp.value(),
                "end_pause": self.end_pause_sp.value(),
                "j_wpm": self.j_wpm.value(), "j_typo": self.j_typo.value(),
                "j_pause": self.j_pause.value(), "j_burst": self.j_burst.value(),
                "s_wpm": self.s_wpm.value(), "s_typo": self.s_typo.value(),
                "s_pause": self.s_pause.value(), "s_burst": self.s_burst.value(),
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
            }
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            log.warning("Save settings failed: %s", e)

    def _load_settings(self):
        if not os.path.isfile(SETTINGS_FILE): return
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except: return
        self._loading_settings = True
        try:
            def _set(cb, key, default=""):
                if key in data:
                    idx = cb.findText(data[key])
                    if idx >= 0: cb.setCurrentIndex(idx)
            _set(self.theme_cb, "theme")
            _set(self.font_family_cb, "font_family")
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
                for k in ["wpm", "typo", "pause", "burst"]:
                    key = f"{pfx}_{k}"
                    if key in data:
                        w = getattr(self, key)
                        w.setValue(float(data[key]) if k != "wpm" else int(data[key]))
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
        finally:
            self._loading_settings = False

    def closeEvent(self, event):
        self._save_settings()
        self._stop_preview_anim()
        if self._exporter:
            self._exporter.cancel()
            self._exporter.wait(5000)
        super().closeEvent(event)

# =====================================================================
# 14. APPLICATION ENTRY POINT
# =====================================================================
STYLE = """
QMainWindow, QDialog { background: #1e1e2e; }
QGroupBox {
    color: #cdd6f4; font-weight: bold; font-size: 13px;
    border: 1px solid #45475a; border-radius: 8px;
    margin-top: 12px; padding-top: 16px;
}
QGroupBox::title { subcontrol-origin: margin; left: 12px; }
QLabel { color: #cdd6f4; }
QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox {
    background: #313244; color: #cdd6f4; border: 1px solid #45475a;
    border-radius: 4px; padding: 4px 8px; min-height: 24px;
}
QComboBox::drop-down { border: none; }
QComboBox QAbstractItemView {
    background: #313244; color: #cdd6f4; selection-background-color: #45475a;
}
QCheckBox { color: #cdd6f4; spacing: 6px; }
QCheckBox::indicator {
    width: 18px; height: 18px; border-radius: 4px;
    border: 2px solid #45475a; background: #313244;
}
QCheckBox::indicator:checked { background: #89b4fa; border-color: #89b4fa; }
QPushButton {
    background: #313244; color: #cdd6f4; border: 1px solid #45475a;
    border-radius: 6px; padding: 6px 16px; font-size: 13px;
}
QPushButton:hover { background: #45475a; }
QProgressBar {
    background: #313244; border: none; border-radius: 4px;
    text-align: center; color: #cdd6f4; min-height: 20px;
}
QProgressBar::chunk { background: #89b4fa; border-radius: 4px; }
QTabWidget::pane {
    border: 1px solid #45475a; border-radius: 6px; background: #1e1e2e; top: -1px;
}
QTabBar::tab {
    background: #313244; color: #a6adc8; padding: 8px 18px;
    border: 1px solid #45475a; border-bottom: none;
    border-top-left-radius: 6px; border-top-right-radius: 6px;
    font-size: 12px; font-weight: bold; margin-right: 2px;
}
QTabBar::tab:selected { background: #1e1e2e; color: #cdd6f4; border-bottom: 2px solid #89b4fa; }
QTabBar::tab:hover:!selected { background: #45475a; color: #cdd6f4; }
QStatusBar { color: #a6adc8; font-size: 12px; }
QListView { background: #181825; color: #cdd6f4; border: none; outline: none; }
QListView::item { padding: 6px 12px; border-bottom: 1px solid #11111b; }
QListView::item:selected { background: #89b4fa; color: #1e1e2e; }
QSlider::groove:horizontal { background: #313244; height: 4px; border-radius: 2px; }
QSlider::handle:horizontal { background: #89b4fa; width: 14px; height: 14px; margin: -5px 0; border-radius: 7px; }
QSlider::sub-page:horizontal { background: #89b4fa; border-radius: 2px; }
QPlainTextEdit { background: #11111b; color: #cdd6f4; border: 1px solid #45475a; border-radius: 4px; }
"""

def main():
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