# Copyright 2026 Huan Jin
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import asyncio
from dotenv import load_dotenv

load_dotenv()
import base64
import hashlib
import io
import json
import os
import random
import re
import atexit
import smtplib
import socket
import subprocess
import psycopg
import psycopg.sql
from psycopg.rows import dict_row
import urllib.request
from datetime import date, datetime, timedelta
from decimal import Decimal
from email.message import EmailMessage

# Hard-coded admin destination for contact-us messages (per product spec).
ADMIN_CONTACT_EMAIL = "jinhuanjoy@gmail.com"

import bcrypt
import edge_tts
import hmac as _hmac
from flask import Flask, Response, g, jsonify, redirect, render_template, request, session, url_for
from characters import CHARACTERS
from words import WORDS

# --- Build lesson/unit structure for grades that have lesson tags ---
# Parse comments from words.py source to extract lesson mapping
LESSON_DATA = {}  # grade -> {lesson_num -> {"识字": [...], "词语": [...]}}
UNIT_MAP = {}     # grade -> {unit_name -> [lesson_nums]}


def _build_lesson_data():
    """Parse words.py source comments to build lesson structure."""
    import re
    words_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "words.py")
    with open(words_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    grade = None
    current_tag = None  # (type, lesson_num)
    grade_data = {}

    for line in lines:
        s = line.strip()
        # Detect grade section
        gm = re.match(r'"([\u4e00-\u9fff]+)":\s*\[', s)
        if gm:
            if grade and grade_data:
                LESSON_DATA[grade] = grade_data
            grade = gm.group(1)
            grade_data = {}
            current_tag = None
            continue

        # Detect lesson comment
        cm = re.match(r'#\s*(识字表|词语表)\s*-\s*第(\d+)课', s)
        if cm:
            table_type = "识字" if cm.group(1) == "识字表" else "词语"
            lesson_num = int(cm.group(2))
            current_tag = (table_type, lesson_num)
            if lesson_num not in grade_data:
                grade_data[lesson_num] = {"识字": [], "词语": []}
            continue

        # Skip 语文园地 comments
        if re.match(r'#\s*(识字表|词语表)\s*-\s*语文园地', s):
            current_tag = None
            continue

        # Parse word entry
        wm = re.match(r'\{"word":\s*"(.+?)",\s*"pinyin":\s*"(.+?)"\}', s)
        if wm and current_tag:
            table_type, lesson_num = current_tag
            grade_data[lesson_num][table_type].append({
                "word": wm.group(1), "pinyin": wm.group(2),
            })

    if grade and grade_data:
        LESSON_DATA[grade] = grade_data



_build_lesson_data()

# --- Build homework lesson structure for ALL grades ---
HOMEWORK_LESSONS = {}  # grade -> {lesson_num: {"识字": [...], "词语": [...]}}

GRADE_ORDER = [
    "一年级上", "一年级下", "二年级上", "二年级下",
    "三年级上", "三年级下", "四年级上", "四年级下",
    "五年级上", "五年级下", "六年级上", "六年级下",
]


def _build_homework_lessons():
    """Build homework lesson data for all grades, auto-chunking where needed."""
    CHUNK_SIZE = 10
    for grade in CHARACTERS:
        if grade in LESSON_DATA and LESSON_DATA[grade]:
            HOMEWORK_LESSONS[grade] = LESSON_DATA[grade]
        else:
            chars = CHARACTERS.get(grade, [])
            words_list = WORDS.get(grade, [])
            char_entries = [{"word": c["char"], "pinyin": c["pinyin"]} for c in chars]
            ciyu_list = [w for w in words_list if len(w["word"]) >= 2]
            char_chunks = [char_entries[i:i + CHUNK_SIZE] for i in range(0, len(char_entries), CHUNK_SIZE)]
            word_chunks = [ciyu_list[i:i + CHUNK_SIZE] for i in range(0, len(ciyu_list), CHUNK_SIZE)]
            num_lessons = max(len(char_chunks), len(word_chunks), 1)
            lessons = {}
            for i in range(num_lessons):
                ln = i + 1
                shizi = char_chunks[i] if i < len(char_chunks) else []
                ciyu = word_chunks[i] if i < len(word_chunks) else []
                lessons[ln] = {"识字": shizi, "词语": ciyu}
            HOMEWORK_LESSONS[grade] = lessons

    # Build combined recognition pool per lesson (识字表 + 写字表 all entries)
    for grade, lessons in HOMEWORK_LESSONS.items():
        for ln, data in lessons.items():
            combined = list(data.get("识字", []))
            for entry in data.get("词语", []):
                # Add individual characters from 词语 that aren't already in 识字
                existing_chars = {e["word"] for e in combined}
                if len(entry["word"]) == 1 and entry["word"] not in existing_chars:
                    combined.append(entry)
                elif len(entry["word"]) >= 2:
                    # Also add multi-char words for pinyin annotation practice
                    combined.append(entry)
            data["认字"] = combined


_build_homework_lessons()


# --- Multi-pronunciation character detection (多音字) ---
MULTI_PINYIN = {}  # char -> set of pinyins (only true multi-pronunciation chars)

# The curated 多音字 hints (MULTI_PINYIN_EXAMPLES) and 同音词 hints
# (HOMOPHONE_HINTS) now live in pinyin_hints.py so the teacher can edit
# them without touching backend code. See that file's header comments
# for the format and editing guidelines.
from pinyin_hints import HOMOPHONE_HINTS, MULTI_PINYIN_EXAMPLES  # noqa: E402,F401


def _pinyin_has_other_word(pinyin: str, target_word: str) -> bool:
    """True if any other multi-char word in WORDS shares this pinyin."""
    for ws in WORDS.values():
        for w in ws:
            if (len(w["word"]) >= 2
                    and w["pinyin"] == pinyin
                    and w["word"] != target_word):
                return True
    return False


def _build_multi_pinyin():
    """Detect characters that have genuinely different pronunciations across the data."""
    tone_map = {
        "ā": "a", "á": "a", "ǎ": "a", "à": "a",
        "ē": "e", "é": "e", "ě": "e", "è": "e",
        "ī": "i", "í": "i", "ǐ": "i", "ì": "i",
        "ō": "o", "ó": "o", "ǒ": "o", "ò": "o",
        "ū": "u", "ú": "u", "ǔ": "u", "ù": "u",
        "ǖ": "ü", "ǘ": "ü", "ǚ": "ü", "ǜ": "ü",
    }

    def strip_tones(p):
        return "".join(tone_map.get(c, c) for c in p.lower())

    def has_tone_mark(p):
        return any(c in tone_map for c in p)

    # Collect all pinyins per character
    char_pinyins: dict[str, set[str]] = {}
    for grade, chars in CHARACTERS.items():
        for c in chars:
            char_pinyins.setdefault(c["char"], set()).add(c["pinyin"])
    for grade, words in WORDS.items():
        for w in words:
            syllables = w["pinyin"].split()
            if len(w["word"]) == len(syllables):
                for ch, py in zip(w["word"], syllables):
                    char_pinyins.setdefault(ch, set()).add(py)

    # Filter to true multi-pronunciation (different base syllables or multiple toned variants)
    for ch, pys in char_pinyins.items():
        if len(pys) < 2:
            continue
        bases = {strip_tones(p) for p in pys}
        if len(bases) > 1:
            MULTI_PINYIN[ch] = pys
            continue
        toned = [p for p in pys if has_tone_mark(p)]
        if len(toned) > 1:
            MULTI_PINYIN[ch] = pys


_build_multi_pinyin()

# Merge curated examples into MULTI_PINYIN so every common primary-school
# 多音字 is flagged as polyphonic even when our WORDS data only happens to
# include one of its readings.
for _ch, _readings in MULTI_PINYIN_EXAMPLES.items():
    existing = MULTI_PINYIN.get(_ch, set())
    existing.update(_readings.keys())
    if len(existing) >= 2:
        MULTI_PINYIN[_ch] = existing


# --- Toned-variant index (for synthesizing multi-char pinyin distractors) ---
# base toneless syllable -> {toned pinyin forms actually seen in our corpus}.
# Lets us build plausible wrong-tone distractors like huā -> huá.
PINYIN_VARIANTS_BY_BASE: dict[str, set[str]] = {}


def _build_pinyin_variants():
    _tone_flat = {
        "ā": "a", "á": "a", "ǎ": "a", "à": "a",
        "ē": "e", "é": "e", "ě": "e", "è": "e",
        "ī": "i", "í": "i", "ǐ": "i", "ì": "i",
        "ō": "o", "ó": "o", "ǒ": "o", "ò": "o",
        "ū": "u", "ú": "u", "ǔ": "u", "ù": "u",
        "ǖ": "ü", "ǘ": "ü", "ǚ": "ü", "ǜ": "ü",
    }
    def base(p):
        return "".join(_tone_flat.get(c, c) for c in p.lower())

    def add(py):
        if not py:
            return
        PINYIN_VARIANTS_BY_BASE.setdefault(base(py), set()).add(py)

    for chars in CHARACTERS.values():
        for c in chars:
            add(c["pinyin"])
    for words in WORDS.values():
        for w in words:
            for syl in w["pinyin"].split():
                add(syl)
    for readings in MULTI_PINYIN_EXAMPLES.values():
        for py in readings:
            add(py)


_build_pinyin_variants()


# --- 形近字 (visually similar characters) lookup ---
# Hand-curated groups of characters that primary-school students easily confuse
# because they share a radical / component or have very similar structure.
# Each string is a group where every char is 形近 to every other in that group.
# Extend this list as needed; 3000+ chars would ideally come from an IDS
# decomposition database, but a curated list covers the most common confusions.
_SHAPE_GROUPS = [
    "己已巳", "未末", "土士", "干于", "人入八", "大太天夫犬",
    "白百", "日曰目", "木本末禾术", "月用", "田由甲申电",
    "千干午牛", "刀力", "手毛", "小少", "心必", "水永",
    "问闻间", "休体", "玩完元园", "青清请情晴睛蜻",
    "跟根很恨银", "吸级极", "圆园圈", "住往", "买卖",
    "找我戏", "比北", "东车乐", "去云丢", "先洗",
    "跑泡抱炮饱袍", "码妈吗骂蚂", "江红工功攻",
    "球求", "衣农", "到倒", "办为", "中忠钟种",
    "爬抓瓜", "处外", "乌鸟岛", "牙与", "巴吧把爸爬",
    "主注住往", "方放访纺", "请情晴睛", "晴情请清",
    "看着", "在再", "从人", "几儿", "又叉",
    "勺匀均", "人从众", "口吕品", "木林森", "水淼",
    "火炎焱", "日昌晶", "夕多", "土圭", "石磊",
    "他她它", "吃乞", "今令冷", "向响", "贝贯",
    "竹笨", "书输", "米粉", "羊洋样", "草早",
    "花化", "鸡鸭", "苗描猫瞄", "睛晴情请清静",
    "跟银狠恨很", "银跟根", "忘望", "吃汔",
    "睡垂", "办为万", "字学", "孩该",
    "汗汉", "快块", "坐座", "朋明", "阳阴",
    "做作", "找钱", "饭板", "妈奶", "弟第",
    "桃跳", "请情", "园圆", "冷今令",
    "包饱抱跑", "青情请清晴睛", "工红空江",
    "每海梅", "可河何", "广床", "开井",
    "公松", "云会", "夕岁", "力另男",
    "是题", "分盆", "半伴", "羊美",
    "会合", "京就", "同洞", "相想",
    "旦早", "也地他", "真直", "自白",
    "且具直", "首道", "安案",
]

SIMILAR_SHAPE: dict[str, set[str]] = {}
for _g in _SHAPE_GROUPS:
    for _ch in _g:
        SIMILAR_SHAPE.setdefault(_ch, set()).update(c for c in _g if c != _ch)


# --- Pinyin initial (声母) / final (韵母) parsing ---
_PINYIN_INITIALS_2 = ("zh", "ch", "sh")
_PINYIN_INITIALS_1 = set("bpmfdtnlgkhjqxrzcsyw")


def _pinyin_initial(pinyin_str: str) -> str:
    """Return the initial consonant (声母) of the first syllable, toneless."""
    base = _strip_tone(pinyin_str or "").strip().lower().split(" ")[0] if pinyin_str else ""
    if not base:
        return ""
    for d in _PINYIN_INITIALS_2:
        if base.startswith(d):
            return d
    if base[0] in _PINYIN_INITIALS_1:
        return base[0]
    return ""


def _pinyin_final(pinyin_str: str) -> str:
    """Return the final (韵母) of the first syllable, toneless."""
    base = _strip_tone(pinyin_str or "").strip().lower().split(" ")[0] if pinyin_str else ""
    initial = _pinyin_initial(pinyin_str)
    return base[len(initial):] if base else ""


def _find_context_word(char: str, pinyin: str, grade: str, lesson_num: int) -> str:
    """Find a context hint for a polyphonic character reading.

    The hint must do two things: confirm the exact pinyin being asked, and
    convey what that reading *means* so the student can tell it apart from
    the char's other readings. A bare lesson word ("行走") does neither —
    the student can't derive the meaning without already knowing the
    reading. So when we have a curated gloss for this (char, pinyin), that
    wins. Only for polyphonic chars we don't have curated data for do we
    fall back to searching lesson / grade / CHARACTERS for a matching
    word.

    Search order:
      1) MULTI_PINYIN_EXAMPLES — curated word + gloss per reading
      2) current lesson 词语 (matching pinyin)
      3) current lesson 识字 multi-char entries (matching pinyin)
      4) WORDS[grade] — grade-level 词语
      5) WORDS across all other grades
      6) CHARACTERS[grade]["words"] — only if pinyin matches
    """
    # 1. Curated hint wins — it's the only source with a disambiguating gloss.
    ex = MULTI_PINYIN_EXAMPLES.get(char, {}).get(pinyin, "")
    if ex:
        return ex

    lesson_data = HOMEWORK_LESSONS.get(grade, {}).get(lesson_num, {})

    def _match_in_word(word: str, word_pinyin: str) -> bool:
        """True if `char` appears in `word` with `pinyin` as its syllable."""
        syllables = word_pinyin.split()
        if len(word) != len(syllables):
            return False
        for ch, py in zip(word, syllables):
            if ch == char and py == pinyin:
                return True
        return False

    # 2. Current lesson 词语
    for entry in lesson_data.get("词语", []):
        if _match_in_word(entry["word"], entry["pinyin"]):
            return entry["word"]

    # 3. Current lesson 识字 (multi-char only)
    for entry in lesson_data.get("识字", []):
        if len(entry["word"]) >= 2 and _match_in_word(entry["word"], entry["pinyin"]):
            return entry["word"]

    # 4. Current grade's WORDS — multi-char only (skip 识字表 single chars)
    for w in WORDS.get(grade, []):
        if len(w["word"]) >= 2 and _match_in_word(w["word"], w["pinyin"]):
            return w["word"]

    # 5. Multi-char WORDS across all other grades
    for g, ws in WORDS.items():
        if g == grade:
            continue
        for w in ws:
            if len(w["word"]) >= 2 and _match_in_word(w["word"], w["pinyin"]):
                return w["word"]

    # 6. CHARACTERS example words — only if the pinyin matches in our data.
    # (The `words` list on a CHARACTERS entry is tied to that entry's single
    # pinyin, so only return it when the question's pinyin matches that
    # canonical reading.)
    for c in CHARACTERS.get(grade, []):
        if c["char"] == char and c["pinyin"] == pinyin and c.get("words"):
            return c["words"][0]

    return ""


def _char_word_examples(char: str, pinyin: str, grade: str) -> list[str]:
    """Return real example words for a single recognition character."""
    if not char or len(char) != 1:
        return []

    def _match_in_word(word: str, word_pinyin: str) -> bool:
        syllables = (word_pinyin or "").split()
        if len(word) != len(syllables):
            return False
        return any(ch == char and py == pinyin for ch, py in zip(word, syllables))

    examples = []

    def _add_matching_words(words):
        for w in words:
            word = w.get("word", "")
            if len(word) >= 2 and _match_in_word(word, w.get("pinyin", "")) and word not in examples:
                examples.append(word)
            if len(examples) >= 2:
                return True
        return False

    if _add_matching_words(WORDS.get(grade, [])):
        return examples
    for g, ws in WORDS.items():
        if g != grade and _add_matching_words(ws):
            return examples
    if examples:
        return examples

    grade_chars = CHARACTERS.get(grade, [])
    for c in grade_chars:
        if c.get("char") == char and c.get("pinyin") == pinyin and c.get("words"):
            return c.get("words", [])
    for chars in CHARACTERS.values():
        for c in chars:
            if c.get("char") == char and c.get("pinyin") == pinyin and c.get("words"):
                return c.get("words", [])
    if char in MULTI_PINYIN:
        return []
    for c in grade_chars:
        if c.get("char") == char and c.get("words"):
            return c.get("words", [])
    for chars in CHARACTERS.values():
        for c in chars:
            if c.get("char") == char and c.get("words"):
                return c.get("words", [])
    for w in WORDS.get(grade, []):
        word = w.get("word", "")
        if len(word) >= 2 and char in word:
            examples.append(word)
        if len(examples) >= 2:
            return examples
    for ws in WORDS.values():
        for w in ws:
            word = w.get("word", "")
            if len(word) >= 2 and char in word and word not in examples:
                examples.append(word)
            if len(examples) >= 2:
                return examples
    if examples:
        return examples
    return []


def _recognition_word_hint(text: str, pinyin: str, grade: str, existing: str = "") -> str:
    """Normalize recognition hints so a bare character is never shown as 组词."""
    text = _string_value(text)
    existing = _string_value(existing)
    if len(text) != 1:
        return ""
    if text in MULTI_PINYIN:
        context = _find_context_word(text, pinyin, grade, 0)
        if context:
            return context
    if existing and existing != text:
        return existing
    return "、".join(_char_word_examples(text, pinyin, grade))


def find_next_lesson_across_grades(current_grade, current_lesson, content_key):
    """Find the next lesson with content, advancing to next grade if needed.
    Returns (grade, lesson_num) or (None, None) if all exhausted."""
    lessons = HOMEWORK_LESSONS.get(current_grade, {})
    total = len(lessons)
    # Search in current grade first
    for ln in range(current_lesson, total + 1):
        if lessons.get(ln, {}).get(content_key):
            return current_grade, ln
    # Current grade exhausted, try next grades
    idx = GRADE_ORDER.index(current_grade) if current_grade in GRADE_ORDER else -1
    for gi in range(idx + 1, len(GRADE_ORDER)):
        next_grade = GRADE_ORDER[gi]
        next_lessons = HOMEWORK_LESSONS.get(next_grade, {})
        for ln in range(1, len(next_lessons) + 1):
            if next_lessons.get(ln, {}).get(content_key):
                return next_grade, ln
    return None, None


def grade_short_name(grade):
    """Convert '一年级上' to '一上'."""
    if not grade:
        return ""
    return grade[0] + grade[-1]


def lesson_counts_by_grade():
    """Return the parsed homework lesson count for each available book."""
    return {grade: len(HOMEWORK_LESSONS.get(grade, {})) for grade in CHARACTERS.keys()}


# --- 分册复习 (per-book review) support ---
# Each book is split into 7 daily portions. The split is deterministic per
# grade (seeded by grade name) so all students get the same day-N content
# and it stays stable across restarts.
BOOK_REVIEW_DAYS = 7
_BOOK_REVIEW_CACHE: dict = {}


def _split_even(lst, n):
    """Split lst into n contiguous chunks whose sizes differ by at most 1."""
    if n <= 0:
        return []
    if not lst:
        return [[] for _ in range(n)]
    size, rem = divmod(len(lst), n)
    out = []
    i = 0
    for k in range(n):
        s = size + (1 if k < rem else 0)
        out.append(lst[i:i + s])
        i += s
    return out


def get_book_review_split(grade):
    """Return {'recognition': [[day1],[day2],...,[day7]],
               'writing':     [[day1],...,[day7]]} for the given book.

    - recognition pool = 识字表 single chars + 写字表 whole words (Q1=A)
    - writing pool     = 写字表 whole words (only used in 看拼音写字)
    Each entry is a dict {'word': str, 'pinyin': str}.
    Deterministic shuffle so every student sees the same day-N slice.
    """
    if grade in _BOOK_REVIEW_CACHE:
        return _BOOK_REVIEW_CACHE[grade]

    chars = CHARACTERS.get(grade, []) or []
    words = WORDS.get(grade, []) or []

    recognition_pool = [
        {"word": c["char"], "pinyin": c["pinyin"]} for c in chars
    ] + [
        {"word": w["word"], "pinyin": w["pinyin"]} for w in words
    ]
    # 看拼音写词语 must be multi-character only — single hanzi are ambiguous
    # when dictated (many homophones), so restrict to 2+ char 词语 only.
    writing_pool = [
        {"word": w["word"], "pinyin": w["pinyin"]}
        for w in words if len(w["word"]) >= 2
    ]

    # Deterministic shuffle keyed on grade name
    random.Random(f"book_review::rec::{grade}").shuffle(recognition_pool)
    random.Random(f"book_review::wrt::{grade}").shuffle(writing_pool)

    result = {
        "recognition": _split_even(recognition_pool, BOOK_REVIEW_DAYS),
        "writing": _split_even(writing_pool, BOOK_REVIEW_DAYS),
    }
    _BOOK_REVIEW_CACHE[grade] = result
    return result


def find_next_book_review_day(grade, current_day, hw_type):
    """Find the next non-empty book-review day for this grade/type."""
    key = "recognition" if hw_type == "recognition" else "writing"
    split = get_book_review_split(grade).get(key, [])
    for day in range(current_day + 1, BOOK_REVIEW_DAYS + 1):
        if day - 1 < len(split) and split[day - 1]:
            return day
    return None


DEFAULT_COIN_RULES = {
    "recognition": [
        {"streak": 15, "coins": 1},
        {"streak": 30, "coins": 3},
        {"streak": 45, "coins": 5},
    ],
    "writing": [
        {"streak": 5, "coins": 2},
        {"streak": 10, "coins": 10},
        {"streak": 20, "coins": 25},
    ],
}

DEFAULT_EXCHANGE_PACKAGES = [
    {"price": 15, "minutes": 20},
    {"price": 20, "minutes": 30},
    {"price": 35, "minutes": 50},
]

COIN_STREAK_LOOKBACK_BOOKS = 3
COIN_INELIGIBLE_MESSAGE = "超过范围，不参与金币连击计算"


def _get_coin_rules(db):
    row = db.execute("SELECT value FROM settings WHERE key = 'coin_rules'").fetchone()
    if row:
        try:
            return json.loads(row["value"])
        except (json.JSONDecodeError, TypeError):
            pass
    return DEFAULT_COIN_RULES


def _get_exchange_packages(db):
    row = db.execute("SELECT value FROM settings WHERE key = 'exchange_packages'").fetchone()
    if row:
        try:
            pkgs = json.loads(row["value"])
            # Add id and name for API compatibility
            for i, p in enumerate(pkgs):
                p["id"] = i + 1
                p["name"] = f"{p['minutes']}分钟游戏时间"
            return pkgs
        except (json.JSONDecodeError, TypeError):
            pass
    pkgs = [dict(p) for p in DEFAULT_EXCHANGE_PACKAGES]
    for i, p in enumerate(pkgs):
        p["id"] = i + 1
        p["name"] = f"{p['minutes']}分钟游戏时间"
    return pkgs


def calc_streak_coins(streak, is_writing, db):
    """Calculate cumulative coins earned from streak milestones, cycling after max.

    E.g. recognition milestones [15→1, 30→3, 45→5]: one full cycle = 9 coins.
    Streak 60 = 1 full cycle (45) + partial (15) = 9 + 1 = 10 coins total.
    """
    rules = _get_coin_rules(db)
    milestones = rules.get("writing" if is_writing else "recognition", [])
    if not milestones:
        return 0
    max_streak = max(m["streak"] for m in milestones)
    coins_per_cycle = sum(m["coins"] for m in milestones)
    full_cycles = streak // max_streak if max_streak > 0 else 0
    remainder = streak % max_streak if max_streak > 0 else streak
    coins = full_cycles * coins_per_cycle
    for m in milestones:
        if remainder >= m["streak"]:
            coins += m["coins"]
    return coins


app = Flask(__name__)

# Custom JSON provider to handle PostgreSQL types (date, Decimal, etc.)
from flask.json.provider import DefaultJSONProvider

class CustomJSONProvider(DefaultJSONProvider):
    def default(self, o):
        if isinstance(o, (date, datetime)):
            return o.isoformat()
        if isinstance(o, Decimal):
            return int(o) if o == int(o) else float(o)
        return super().default(o)

app.json_provider_class = CustomJSONProvider
app.json = CustomJSONProvider(app)

_secret = os.environ.get("SECRET_KEY")
if not _secret:
    raise RuntimeError("SECRET_KEY environment variable must be set")
app.secret_key = _secret
app.config["SESSION_PERMANENT"] = True
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=30)

ADMIN_PASSWORD_HASH = os.environ.get("ADMIN_PASSWORD_HASH", "")
_legacy_admin_pw = os.environ.get("ADMIN_PASSWORD", "")
if not ADMIN_PASSWORD_HASH and not _legacy_admin_pw:
    raise RuntimeError("ADMIN_PASSWORD_HASH environment variable must be set")

DATABASE_URL = os.environ.get("DATABASE_URL", "postgresql://localhost/hanzi_db")

# --- SSH Tunnel ---
SSH_TUNNEL_HOST = os.environ.get("SSH_TUNNEL_HOST")
SSH_TUNNEL_USER = os.environ.get("SSH_TUNNEL_USER", "ubuntu")
SSH_TUNNEL_PORT = int(os.environ.get("SSH_TUNNEL_PORT", "22"))
SSH_KEY_PATH = os.environ.get("SSH_KEY_PATH")
ssh_tunnel_proc = None

if SSH_TUNNEL_HOST:
    # Pick a free local port
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        local_port = s.getsockname()[1]
    ssh_cmd = [
        "ssh", "-N", "-L",
        f"{local_port}:127.0.0.1:5432",
        "-p", str(SSH_TUNNEL_PORT),
        "-o", "StrictHostKeyChecking=accept-new",
        "-o", "ExitOnForwardFailure=yes",
    ]
    if SSH_KEY_PATH:
        ssh_cmd += ["-i", os.path.expanduser(SSH_KEY_PATH)]
    ssh_cmd.append(f"{SSH_TUNNEL_USER}@{SSH_TUNNEL_HOST}")
    ssh_tunnel_proc = subprocess.Popen(
        ssh_cmd,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    atexit.register(ssh_tunnel_proc.terminate)
    # Wait for tunnel to be ready
    import time
    for _ in range(30):
        if ssh_tunnel_proc.poll() is not None:
            err = ssh_tunnel_proc.stderr.read().decode()
            raise RuntimeError(f"SSH tunnel failed: {err}")
        try:
            with socket.create_connection(("127.0.0.1", local_port), timeout=1):
                break
        except OSError:
            time.sleep(0.5)
    else:
        ssh_tunnel_proc.terminate()
        raise RuntimeError("SSH tunnel timed out waiting for connection")
    DATABASE_URL = DATABASE_URL.replace(
        "localhost:5432", f"localhost:{local_port}"
    )


def get_db():
    if "db" not in g:
        g.db = psycopg.connect(DATABASE_URL, row_factory=dict_row)
    return g.db


@app.teardown_appcontext
def close_db(exc):
    db = g.pop("db", None)
    if db is not None:
        db.close()


# --- Security headers ---
@app.after_request
def set_security_headers(response):
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["X-XSS-Protection"] = "1; mode=block"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    if request.is_secure:
        response.headers["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
    return response


# --- CSRF protection ---
CSRF_SAFE_METHODS = frozenset(("GET", "HEAD", "OPTIONS"))

def _generate_csrf_token():
    if "_csrf_token" not in session:
        session["_csrf_token"] = os.urandom(32).hex()
    return session["_csrf_token"]

# Make csrf_token available in all templates
app.jinja_env.globals["csrf_token"] = _generate_csrf_token

@app.before_request
def csrf_protect():
    if request.method in CSRF_SAFE_METHODS:
        return
    # Skip CSRF for login/register (no session yet) and handwriting (external API proxy)
    CSRF_EXEMPT = ("/api/login", "/api/register", "/api/handwriting", "/api/admin/login")
    if request.path in CSRF_EXEMPT:
        return
    # For JSON API requests, Content-Type: application/json is sufficient CSRF protection
    # (browsers don't send JSON cross-origin without CORS preflight)
    ct = request.content_type or ""
    if ct.startswith("application/json"):
        return
    token = (
        request.headers.get("X-CSRF-Token")
        or (request.get_json(silent=True) or {}).get("_csrf_token")
        or request.form.get("_csrf_token")
    )
    if not token or not _hmac.compare_digest(token, session.get("_csrf_token", "")):
        return jsonify({"error": "CSRF token missing or invalid"}), 403


# --- Rate limiting ---
_rate_limit_store: dict = {}  # key -> (count, window_start)

def _rate_limited(key: str, max_requests: int, window_seconds: int) -> bool:
    """Simple in-process rate limiter. Returns True if over limit."""
    now = datetime.now().timestamp()
    entry = _rate_limit_store.get(key)
    if entry is None or now - entry[1] > window_seconds:
        _rate_limit_store[key] = (1, now)
        return False
    count, start = entry
    if count >= max_requests:
        return True
    _rate_limit_store[key] = (count + 1, start)
    return False


MODE_LABELS = {
    "char_to_pinyin": "看字选拼音",
    "pinyin_to_char": "看拼音选字",
    "listen_to_char": "听音选字",
    "pinyin_typing": "给汉字注音",
    "dictation_handwrite": "看拼音写词语",
    "read_aloud": "看字读音",
}

HW_TYPE_LABELS = {"recognition": "认字", "writing": "写字"}


def _string_value(value) -> str:
    return "" if value is None else str(value)


def _wrong_item_payload(item, fallback_grade="", fallback_mode=""):
    """Normalize old and new wrong-item payloads into one immutable event shape."""
    item = item or {}
    mode = _string_value(item.get("mode") or fallback_mode)
    character = _string_value(item.get("character") or item.get("display_char"))
    pinyin = _string_value(item.get("pinyin") or item.get("display_pinyin"))
    question = _string_value(item.get("question"))
    correct_answer = _string_value(item.get("correct_answer") or item.get("answer"))
    user_answer = _string_value(item.get("user_answer") or item.get("userAnswer"))
    words = _string_value(item.get("words") or item.get("word_hint"))
    grade = _string_value(item.get("grade") or fallback_grade)

    if not character:
        if mode in ("pinyin_to_char", "listen_to_char", "dictation_handwrite"):
            character = correct_answer
        elif mode in ("char_to_pinyin", "pinyin_typing", "read_aloud"):
            character = question
    if not pinyin:
        if mode in ("char_to_pinyin", "pinyin_typing", "read_aloud"):
            pinyin = correct_answer
        else:
            pinyin = question
    if not question:
        question = pinyin if mode in ("pinyin_to_char", "dictation_handwrite") else character
    if not correct_answer:
        correct_answer = pinyin if mode in ("char_to_pinyin", "pinyin_typing", "read_aloud") else character
    if mode != "dictation_handwrite":
        words = _recognition_word_hint(character, pinyin, grade, words)

    return {
        "character": character,
        "pinyin": pinyin,
        "words": words,
        "grade": grade,
        "mode": mode,
        "question": question,
        "correct_answer": correct_answer,
        "user_answer": user_answer,
    }


def _source_label(source, grade="", mode="", assignment_type="", lesson_num=None, assignment_mode=""):
    if source == "homework":
        type_label = HW_TYPE_LABELS.get(assignment_type, "作业")
        unit = "天" if assignment_mode == "book_review" else "课"
        if lesson_num:
            return f"{grade_short_name(grade)}{type_label}作业 · 第{lesson_num}{unit}"
        return f"{grade_short_name(grade)}{type_label}作业"
    if source == "game":
        mode_label = MODE_LABELS.get(mode, mode)
        return f"自由练习 · {grade_short_name(grade)} · {mode_label}"
    if source == "wrong_answers":
        mode_label = MODE_LABELS.get(mode, mode)
        return f"既有错题记录 · {grade_short_name(grade)} · {mode_label}"
    return source or "未知来源"


def _insert_wrong_event(db, user_id, item, *, source, source_id=None, source_date=None,
                        source_label="", event_key=None, fallback_grade="",
                        fallback_mode="", created_at=None):
    payload = _wrong_item_payload(item, fallback_grade=fallback_grade, fallback_mode=fallback_mode)
    if not payload["character"] and not payload["question"]:
        return
    source_date = _string_value(source_date or date.today().isoformat())
    if isinstance(created_at, str):
        try:
            created_at = datetime.fromisoformat(created_at)
        except ValueError:
            created_at = None
    db.execute(
        """INSERT INTO wrong_answer_events
           (event_key, user_id, character, pinyin, words, grade, mode, source,
            source_id, source_date, source_label, question, correct_answer,
            user_answer, created_at)
           VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s,
                   COALESCE(%s, CURRENT_TIMESTAMP))
           ON CONFLICT (event_key) DO NOTHING""",
        (
            event_key,
            user_id,
            payload["character"],
            payload["pinyin"],
            payload["words"],
            payload["grade"],
            payload["mode"],
            source,
            source_id,
            source_date,
            source_label,
            payload["question"],
            payload["correct_answer"],
            payload["user_answer"],
            created_at,
        ),
    )


def _backfill_wrong_answer_events(db):
    """Backfill immutable wrong history from records we can still trace."""
    assignments = db.execute(
        """SELECT id, user_id, date, type, grade, lesson_num, mode, wrong_items,
                  completed_at, created_at
           FROM daily_assignments
           WHERE status = 'completed'
             AND wrong_items IS NOT NULL
             AND wrong_items != ''
             AND wrong_items != '[]'"""
    ).fetchall()
    for assignment in assignments:
        try:
            items = json.loads(assignment["wrong_items"])
        except Exception:
            items = []
        if not isinstance(items, list):
            continue
        source_label = _source_label(
            "homework",
            grade=assignment["grade"],
            assignment_type=assignment["type"],
            lesson_num=assignment["lesson_num"],
            assignment_mode=assignment["mode"],
        )
        created_at = assignment["completed_at"] or assignment["created_at"] or assignment["date"]
        for idx, item in enumerate(items):
            payload = _wrong_item_payload(item, fallback_grade=assignment["grade"])
            event_key = f"homework:{assignment['id']}:{idx}:{payload['character']}:{payload['mode']}"
            _insert_wrong_event(
                db,
                assignment["user_id"],
                item,
                source="homework",
                source_id=assignment["id"],
                source_date=assignment["date"],
                source_label=source_label,
                event_key=event_key,
                fallback_grade=assignment["grade"],
                created_at=created_at,
            )

    rows = db.execute(
        """SELECT id, user_id, character, pinyin, words, grade, mode, created_at
           FROM wrong_answers"""
    ).fetchall()
    for row in rows:
        source_date = row["created_at"].date().isoformat() if hasattr(row["created_at"], "date") else str(row["created_at"])[:10]
        exists = db.execute(
            """SELECT 1 FROM wrong_answer_events
               WHERE user_id = %s AND source_date = %s
                 AND character = %s AND mode = %s
               LIMIT 1""",
            (row["user_id"], source_date, row["character"], row["mode"]),
        ).fetchone()
        if exists:
            continue
        item = dict(row)
        _insert_wrong_event(
            db,
            row["user_id"],
            item,
            source="wrong_answers",
            source_id=row["id"],
            source_date=source_date,
            source_label=_source_label("wrong_answers", grade=row["grade"], mode=row["mode"]),
            event_key=f"wrong_answers:{row['id']}",
            fallback_grade=row["grade"],
            fallback_mode=row["mode"],
            created_at=row["created_at"],
        )


def _parse_exchange_minutes(details):
    match = re.search(r"兑换\s*(\d+)\s*分钟", details or "")
    if not match:
        match = re.search(r"(\d+)\s*分钟", details or "")
    return int(match.group(1)) if match else 0


def _backfill_exchange_records(db):
    rows = db.execute(
        """SELECT id, user_id, amount, details, created_at
           FROM coin_transactions
           WHERE source = 'shop' AND amount < 0
           ORDER BY id"""
    ).fetchall()
    for row in rows:
        minutes = _parse_exchange_minutes(row["details"])
        if minutes <= 0:
            continue
        created_at = row["created_at"]
        exchange_date = created_at.date().isoformat() if hasattr(created_at, "date") else str(created_at)[:10]
        db.execute(
            """INSERT INTO exchange_records
               (user_id, exchange_date, coins, minutes, source_transaction_id, created_at)
               VALUES (%s, %s, %s, %s, %s, %s)
               ON CONFLICT (source_transaction_id) DO NOTHING""",
            (row["user_id"], exchange_date, abs(row["amount"]), minutes, row["id"], created_at),
        )


def _seed_linky_game_usage_records(db):
    user = db.execute("SELECT id FROM users WHERE LOWER(username) = 'linky'").fetchone()
    if not user:
        return
    seeds = [
        ("2026-05-13", 100, "还罚款"),
        ("2026-05-13", 50, "玩"),
    ]
    for usage_date, minutes, purpose in seeds:
        exists = db.execute(
            """SELECT 1 FROM game_usage_records
               WHERE user_id = %s AND usage_date = %s AND minutes = %s AND purpose = %s
               LIMIT 1""",
            (user["id"], usage_date, minutes, purpose),
        ).fetchone()
        if exists:
            continue
        db.execute(
            """INSERT INTO game_usage_records (user_id, usage_date, minutes, purpose)
               VALUES (%s, %s, %s, %s)""",
            (user["id"], usage_date, minutes, purpose),
        )


def init_db():
    db = psycopg.connect(DATABASE_URL, row_factory=dict_row)
    # Gunicorn boots multiple workers concurrently and each imports this
    # module, so without serialization the schema migrations and idempotent
    # backfills race and deadlock on wrong_answer_events row locks, crashing
    # every worker. A session-level advisory lock (released when this
    # connection closes at the end of init_db) makes workers run this
    # one at a time; the backfills are idempotent so the rest just no-op.
    db.execute("SELECT pg_advisory_lock(%s)", (873_421_905,))
    db.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id SERIAL PRIMARY KEY,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS scores (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            grade TEXT NOT NULL,
            mode TEXT NOT NULL,
            score INTEGER NOT NULL,
            combo_max INTEGER NOT NULL DEFAULT 0,
            total_questions INTEGER NOT NULL DEFAULT 0,
            correct_answers INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS wrong_answers (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            character TEXT NOT NULL,
            pinyin TEXT NOT NULL,
            words TEXT NOT NULL,
            grade TEXT NOT NULL,
            mode TEXT NOT NULL,
            review_count INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS wrong_answer_events (
            id SERIAL PRIMARY KEY,
            event_key TEXT UNIQUE,
            user_id INTEGER NOT NULL,
            character TEXT NOT NULL DEFAULT '',
            pinyin TEXT NOT NULL DEFAULT '',
            words TEXT NOT NULL DEFAULT '',
            grade TEXT NOT NULL DEFAULT '',
            mode TEXT NOT NULL DEFAULT '',
            source TEXT NOT NULL DEFAULT '',
            source_id INTEGER,
            source_date TEXT NOT NULL DEFAULT '',
            source_label TEXT NOT NULL DEFAULT '',
            question TEXT NOT NULL DEFAULT '',
            correct_answer TEXT NOT NULL DEFAULT '',
            user_answer TEXT NOT NULL DEFAULT '',
            review_count INTEGER NOT NULL DEFAULT 0,
            mastered INTEGER NOT NULL DEFAULT 0,
            mastered_at TIMESTAMP,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("CREATE INDEX IF NOT EXISTS idx_wrong_events_user_date ON wrong_answer_events(user_id, source_date)")
    db.execute("CREATE INDEX IF NOT EXISTS idx_wrong_events_source ON wrong_answer_events(source, source_id)")
    db.execute("""
        CREATE TABLE IF NOT EXISTS mastered_words (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            character TEXT NOT NULL,
            pinyin TEXT NOT NULL,
            words TEXT NOT NULL,
            grade TEXT NOT NULL,
            mode TEXT NOT NULL,
            review_count INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            mastered_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS shop_items (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            description TEXT DEFAULT '',
            price INTEGER NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS purchases (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            item_id INTEGER NOT NULL,
            purchased_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id),
            FOREIGN KEY (item_id) REFERENCES shop_items(id)
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS settings (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS homework_plans (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            grade TEXT NOT NULL,
            recognition_lesson INTEGER NOT NULL DEFAULT 1,
            writing_lesson INTEGER NOT NULL DEFAULT 1,
            recognition_grade TEXT NOT NULL DEFAULT '',
            writing_grade TEXT NOT NULL DEFAULT '',
            mode TEXT NOT NULL DEFAULT 'by_lesson',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS coin_transactions (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            amount INTEGER NOT NULL,
            source TEXT NOT NULL,
            mode TEXT NOT NULL DEFAULT '',
            grade TEXT NOT NULL DEFAULT '',
            details TEXT NOT NULL DEFAULT '',
            created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("CREATE INDEX IF NOT EXISTS idx_coin_tx_user_date ON coin_transactions(user_id, created_at)")
    db.execute("""
        CREATE TABLE IF NOT EXISTS exchange_records (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            exchange_date TEXT NOT NULL,
            coins INTEGER NOT NULL,
            minutes INTEGER NOT NULL,
            source_transaction_id INTEGER UNIQUE,
            created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("CREATE INDEX IF NOT EXISTS idx_exchange_records_user_date ON exchange_records(user_id, exchange_date)")
    db.execute("""
        CREATE TABLE IF NOT EXISTS game_usage_records (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            usage_date TEXT NOT NULL,
            minutes INTEGER NOT NULL,
            purpose TEXT NOT NULL DEFAULT '',
            created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("CREATE INDEX IF NOT EXISTS idx_game_usage_user_date ON game_usage_records(user_id, usage_date)")
    db.execute("""
        CREATE TABLE IF NOT EXISTS contact_messages (
            id SERIAL PRIMARY KEY,
            user_id INTEGER,
            username TEXT NOT NULL DEFAULT '',
            reply_email TEXT NOT NULL DEFAULT '',
            subject TEXT NOT NULL DEFAULT '',
            message TEXT NOT NULL,
            email_sent INTEGER NOT NULL DEFAULT 0,
            email_error TEXT NOT NULL DEFAULT '',
            created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
    """)
    db.execute("CREATE INDEX IF NOT EXISTS idx_contact_created ON contact_messages(created_at)")
    db.execute("""
        CREATE TABLE IF NOT EXISTS daily_assignments (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            date TEXT NOT NULL,
            type TEXT NOT NULL,
            grade TEXT NOT NULL,
            lesson_num INTEGER NOT NULL,
            mode TEXT NOT NULL DEFAULT 'by_lesson',
            status TEXT NOT NULL DEFAULT 'pending',
            total_questions INTEGER NOT NULL DEFAULT 0,
            correct_answers INTEGER NOT NULL DEFAULT 0,
            time_spent INTEGER NOT NULL DEFAULT 0,
            wrong_items TEXT NOT NULL DEFAULT '[]',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            completed_at TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    # Migrate: add columns if missing
    def _col_exists(table, column):
        row = db.execute(
            "SELECT 1 FROM information_schema.columns WHERE table_name = %s AND column_name = %s",
            (table, column),
        ).fetchone()
        return row is not None

    if not _col_exists("scores", "total_questions"):
        db.execute("ALTER TABLE scores ADD COLUMN total_questions INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("scores", "correct_answers"):
        db.execute("ALTER TABLE scores ADD COLUMN correct_answers INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("wrong_answers", "review_count"):
        db.execute("ALTER TABLE wrong_answers ADD COLUMN review_count INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("users", "coins"):
        db.execute("ALTER TABLE users ADD COLUMN coins INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("users", "game_minutes"):
        db.execute("ALTER TABLE users ADD COLUMN game_minutes INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("users", "recognition_streak"):
        db.execute("ALTER TABLE users ADD COLUMN recognition_streak INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("users", "writing_streak"):
        db.execute("ALTER TABLE users ADD COLUMN writing_streak INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("users", "recognition_coins_awarded"):
        db.execute("ALTER TABLE users ADD COLUMN recognition_coins_awarded INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("users", "writing_coins_awarded"):
        db.execute("ALTER TABLE users ADD COLUMN writing_coins_awarded INTEGER NOT NULL DEFAULT 0")
    # Parental control: each user can set a separate password that grants
    # a read+plan-edit session scoped to just that user's data.
    if not _col_exists("users", "parent_password_hash"):
        db.execute("ALTER TABLE users ADD COLUMN parent_password_hash TEXT NOT NULL DEFAULT ''")
    # Recovery email for password reset codes.
    if not _col_exists("users", "email"):
        db.execute("ALTER TABLE users ADD COLUMN email TEXT NOT NULL DEFAULT ''")
    db.execute("""
        CREATE TABLE IF NOT EXISTS password_reset_codes (
            id SERIAL PRIMARY KEY,
            user_id INTEGER NOT NULL,
            target TEXT NOT NULL,
            code_hash TEXT NOT NULL,
            expires_at TIMESTAMP NOT NULL,
            used INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    # Migrate daily_assignments: add saved_progress for resume support
    if not _col_exists("daily_assignments", "saved_progress"):
        db.execute("ALTER TABLE daily_assignments ADD COLUMN saved_progress TEXT NOT NULL DEFAULT ''")
    # Migrate homework_plans: add separate grade tracking per type
    if not _col_exists("homework_plans", "recognition_grade"):
        db.execute("ALTER TABLE homework_plans ADD COLUMN recognition_grade TEXT NOT NULL DEFAULT ''")
        db.execute("ALTER TABLE homework_plans ADD COLUMN writing_grade TEXT NOT NULL DEFAULT ''")
        # Backfill: copy existing grade to both recognition_grade and writing_grade
        db.execute("UPDATE homework_plans SET recognition_grade = grade, writing_grade = grade")
    # Migrate: add mode column for 分册复习 (book review) plans
    if not _col_exists("homework_plans", "mode"):
        db.execute("ALTER TABLE homework_plans ADD COLUMN mode TEXT NOT NULL DEFAULT 'by_lesson'")
    if not _col_exists("daily_assignments", "mode"):
        db.execute("ALTER TABLE daily_assignments ADD COLUMN mode TEXT NOT NULL DEFAULT 'by_lesson'")
    if not _col_exists("wrong_answer_events", "review_count"):
        db.execute("ALTER TABLE wrong_answer_events ADD COLUMN review_count INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("wrong_answer_events", "mastered"):
        db.execute("ALTER TABLE wrong_answer_events ADD COLUMN mastered INTEGER NOT NULL DEFAULT 0")
    if not _col_exists("wrong_answer_events", "mastered_at"):
        db.execute("ALTER TABLE wrong_answer_events ADD COLUMN mastered_at TIMESTAMP")
    if not _col_exists("contact_messages", "image_name"):
        db.execute("ALTER TABLE contact_messages ADD COLUMN image_name TEXT NOT NULL DEFAULT ''")
    if not _col_exists("contact_messages", "image_mime"):
        db.execute("ALTER TABLE contact_messages ADD COLUMN image_mime TEXT NOT NULL DEFAULT ''")
    if not _col_exists("contact_messages", "image_data"):
        db.execute("ALTER TABLE contact_messages ADD COLUMN image_data TEXT NOT NULL DEFAULT ''")
    _backfill_wrong_answer_events(db)
    _backfill_exchange_records(db)
    _seed_linky_game_usage_records(db)
    db.commit()
    db.close()


def hash_password(password, salt=None):
    """Hash a password using bcrypt. The salt parameter is ignored (bcrypt manages its own)."""
    return bcrypt.hashpw(password.encode(), bcrypt.gensalt()).decode()


def verify_password(password, stored):
    """Verify a password against a stored hash. Supports both bcrypt and legacy SHA-256 hashes."""
    if stored.startswith("$2b$") or stored.startswith("$2a$"):
        return bcrypt.checkpw(password.encode(), stored.encode())
    # Legacy SHA-256 format: salt:hash
    if ":" in stored:
        salt, hashed = stored.split(":", 1)
        return hashlib.sha256((salt + password).encode()).hexdigest() == hashed
    return False


def _migrate_password_if_needed(db, user_id, password, stored):
    """Re-hash a legacy SHA-256 password to bcrypt after successful verification."""
    if stored.startswith("$2b$") or stored.startswith("$2a$"):
        return
    new_hash = hash_password(password)
    db.execute("UPDATE users SET password_hash = %s WHERE id = %s", (new_hash, user_id))


init_db()


def _strip_tone(pinyin: str) -> str:
    """Remove tone marks for grouping similar-sounding syllables."""
    tone_map = {
        "ā": "a", "á": "a", "ǎ": "a", "à": "a",
        "ē": "e", "é": "e", "ě": "e", "è": "e",
        "ī": "i", "í": "i", "ǐ": "i", "ì": "i",
        "ō": "o", "ó": "o", "ǒ": "o", "ò": "o",
        "ū": "u", "ú": "u", "ǔ": "u", "ù": "u",
        "ǖ": "ü", "ǘ": "ü", "ǚ": "ü", "ǜ": "ü",
    }
    return "".join(tone_map.get(c, c) for c in pinyin)


def _generate_question(grade: str, mode: str) -> dict:
    """Generate a quiz question for the given grade and mode."""
    char_list = CHARACTERS.get(grade, [])
    if len(char_list) < 4:
        return {"error": "Not enough characters for this grade"}

    correct = random.choice(char_list)
    others = [c for c in char_list if c["char"] != correct["char"]]

    if mode == "char_to_pinyin":
        # Show character, pick correct pinyin from options
        distractors = _pick_distractors(correct, others, key="pinyin")
        options = [correct["pinyin"]] + [d["pinyin"] for d in distractors]
        random.shuffle(options)
        q = {
            "mode": mode,
            "question": correct["char"],
            "options": options,
            "correct_index": options.index(correct["pinyin"]),
            "answer": correct["pinyin"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }
        # For 多音字, show a context word so the reader knows which reading is asked
        if correct["char"] in MULTI_PINYIN:
            cw = _find_context_word(correct["char"], correct["pinyin"], grade, 0)
            if cw:
                q["context_word"] = cw
        return q

    if mode == "pinyin_to_char":
        # Show pinyin, pick correct character from options
        distractors = _pick_distractors(correct, others, key="char")
        options = [correct["char"]] + [d["char"] for d in distractors]
        random.shuffle(options)
        return {
            "mode": mode,
            "question": correct["pinyin"],
            "options": options,
            "correct_index": options.index(correct["char"]),
            "answer": correct["char"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }

    if mode == "listen_to_char":
        # TTS reads the character, pick correct character from options
        # Exclude homophones so the player can distinguish by sound
        distractors = _pick_distractors(correct, others, key="char",
                                        exclude_homophones=True)
        options = [correct["char"]] + [d["char"] for d in distractors]
        random.shuffle(options)
        return {
            "mode": mode,
            "question": correct["char"],
            "question_pinyin": correct["pinyin"],
            "options": options,
            "correct_index": options.index(correct["char"]),
            "answer": correct["char"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }

    if mode == "read_aloud":
        # Show character, user reads aloud — answer is pinyin (with tone marks)
        q = {
            "mode": mode,
            "question": correct["char"],
            "answer": correct["pinyin"],
            "answer_char": correct["char"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }
        if correct["char"] in MULTI_PINYIN:
            cw = _find_context_word(correct["char"], correct["pinyin"], grade, 0)
            if cw:
                q["context_word"] = cw
        return q

    if mode == "pinyin_typing":
        # Show character, handwrite pinyin
        q = {
            "mode": mode,
            "question": correct["char"],
            "answer": correct["pinyin"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
            "display_char": correct["char"],
            "display_pinyin": correct["pinyin"],
        }
        if correct["char"] in MULTI_PINYIN:
            cw = _find_context_word(correct["char"], correct["pinyin"], grade, 0)
            if cw:
                q["context_word"] = cw
        return q

    if mode == "dictation_handwrite":
        word_list = WORDS.get(grade, [])
        # Only pick multi-character words (词语), exclude single characters (识字表).
        # Also drop homophone words lacking a curated disambiguation hint — otherwise
        # the same pinyin can map to multiple valid answers with no way for the
        # student to tell which one to write.
        ciyu_list = [
            w for w in word_list
            if len(w["word"]) >= 2
            and (w["word"] in HOMOPHONE_HINTS
                 or not _pinyin_has_other_word(w["pinyin"], w["word"]))
        ]
        if not ciyu_list:
            return {"error": "该年级暂无词语数据"}
        word_entry = random.choice(ciyu_list)
        q = {
            "mode": mode,
            "question": word_entry["pinyin"],
            "answer": word_entry["word"],
        }
        if _pinyin_has_other_word(word_entry["pinyin"], word_entry["word"]):
            hint = HOMOPHONE_HINTS.get(word_entry["word"])
            if hint:
                q["homophone_hint"] = hint
        return q

    return {"error": f"Unknown mode: {mode}"}


def _pick_distractors(correct: dict, others: list, key: str, count: int = 3,
                      exclude_homophones: bool = False) -> list:
    """Pick distractor options that differ from the correct answer.

    Applies 字数 matching (single-char questions only yield single-char
    distractors; 2-char words only yield 2-char distractors; etc.) and
    prefers harder distractors — 形近字, 同音字, 近音字 — before falling
    back to random same-length picks.
    """
    correct_val = correct[key]
    correct_pinyin = correct.get("pinyin", "")
    correct_char = correct.get("char", "")

    # --- Length / syllable-count matching ---
    # For key="char": distractor chars must have the same number of hanzi.
    # For key="pinyin": distractor pinyins must have the same syllable count
    # (syllables are whitespace-separated in our data).
    if key == "char":
        target_len = len(correct_val)
        def _same_len(c):
            return len(c.get("char", "")) == target_len
    elif key == "pinyin":
        target_sylls = len(correct_val.split())
        def _same_len(c):
            return len(c.get("pinyin", "").split()) == target_sylls
    else:
        def _same_len(c):
            return True

    candidates = [c for c in others if c[key] != correct_val and _same_len(c)]

    if exclude_homophones:
        candidates = [c for c in candidates if c.get("pinyin") != correct_pinyin]

    # --- Priority pools: harder distractors first ---
    priority: list = []
    seen_vals = {correct_val}

    def _add(pool):
        for c in pool:
            v = c[key]
            if v in seen_vals:
                continue
            priority.append(c)
            seen_vals.add(v)

    if key == "char":
        # 1) 形近字 — shape-similar characters (only meaningful for single chars)
        if len(correct_char) == 1:
            shape_sim = SIMILAR_SHAPE.get(correct_char, set())
            if shape_sim:
                _add([c for c in candidates if c.get("char") in shape_sim])
        # 2) 同音字 — exact pinyin match (skip when excluded, e.g. listen mode)
        if not exclude_homophones and correct_pinyin:
            _add([c for c in candidates if c.get("pinyin") == correct_pinyin])
        # 3) 近音字 — same base syllable, different tone
        if correct_pinyin:
            base = _strip_tone(correct_pinyin)
            _add([c for c in candidates if _strip_tone(c.get("pinyin", "")) == base])
        # 4) 同声母 / 同韵母 — further phonetic confusables
        if correct_pinyin:
            initial = _pinyin_initial(correct_pinyin)
            final = _pinyin_final(correct_pinyin)
            if initial:
                _add([c for c in candidates if _pinyin_initial(c.get("pinyin", "")) == initial])
            if final:
                _add([c for c in candidates if _pinyin_final(c.get("pinyin", "")) == final])
    elif key == "pinyin":
        # 1) Tone-variant pinyins (same base syllable)
        base = _strip_tone(correct_val)
        _add([c for c in candidates if _strip_tone(c.get("pinyin", "")) == base])
        # 2) Same initial / same final
        initial = _pinyin_initial(correct_val)
        final = _pinyin_final(correct_val)
        if initial:
            _add([c for c in candidates if _pinyin_initial(c.get("pinyin", "")) == initial])
        if final:
            _add([c for c in candidates if _pinyin_final(c.get("pinyin", "")) == final])

    random.shuffle(priority)
    result = priority[:count]

    # Fill from remaining same-length candidates if priority pools are short
    if len(result) < count:
        used = {c[key] for c in result} | {correct_val}
        remaining = [c for c in candidates if c[key] not in used]
        random.shuffle(remaining)
        result += remaining[:count - len(result)]

    # For multi-char word pinyin questions the same-length 词语 pool is
    # often too small (there are only ~40 3-char and ~60 4-char 词语 in
    # the entire corpus). If we still don't have enough distractors, build
    # synthetic ones by perturbing a single syllable of the correct pinyin
    # — using another reading of a polyphonic char, or a different-tone
    # variant of the same base syllable. These are also the exact
    # misreadings students make, so they're pedagogically better than
    # random same-length noise.
    if key == "pinyin" and len(result) < count and len(correct_char) >= 2:
        existing_vals = {correct_val} | {r[key] for r in result}
        for syn in _synthesize_word_pinyin_distractors(
                correct_char, correct_val, count - len(result)):
            if syn in existing_vals:
                continue
            result.append({"char": correct_char, "pinyin": syn, "words": []})
            existing_vals.add(syn)
            if len(result) >= count:
                break

    return result[:count]


def _synthesize_word_pinyin_distractors(word: str, correct_pinyin: str,
                                        count: int = 3) -> list[str]:
    """Build multi-char distractor pinyins by swapping one syllable.

    Sources of swap candidates, in order:
      1) Other readings of the character when it's polyphonic — these are
         the exact misreadings a student is prone to make.
      2) Other toned variants of the same base syllable seen anywhere in
         our corpus (e.g. huā/huá/huà for 花's syllable).

    Positions are tried in random order so we don't always perturb the
    first character. Returns up to `count` distinct pinyin strings, each
    different from `correct_pinyin`.
    """
    syls = correct_pinyin.split()
    if len(word) != len(syls):
        return []
    out: list[str] = []
    seen = {correct_pinyin}
    positions = list(range(len(word)))
    random.shuffle(positions)
    for pos in positions:
        ch = word[pos]
        cur = syls[pos]
        swaps: list[str] = []
        for alt in MULTI_PINYIN.get(ch, set()):
            if alt != cur and alt not in swaps:
                swaps.append(alt)
        base = _strip_tone(cur)
        for alt in PINYIN_VARIANTS_BY_BASE.get(base, set()):
            if alt != cur and alt not in swaps:
                swaps.append(alt)
        random.shuffle(swaps)
        for alt in swaps:
            new_syls = syls[:pos] + [alt] + syls[pos+1:]
            cand = " ".join(new_syls)
            if cand in seen:
                continue
            out.append(cand)
            seen.add(cand)
            if len(out) >= count:
                return out
    return out


def _generate_lesson_question(grade: str, mode: str, lessons: list) -> dict:
    """Generate a question from specific lessons only."""
    grade_lessons = LESSON_DATA.get(grade, {})
    if not grade_lessons:
        return {"error": "该年级暂无按课数据"}

    # Collect entries from the requested lessons
    shizi_entries = []  # 识字表 single chars
    ciyu_entries = []   # 词语表 compound words
    for ln in lessons:
        ld = grade_lessons.get(ln, {})
        shizi_entries.extend(ld.get("识字", []))
        ciyu_entries.extend(ld.get("词语", []))

    if mode == "dictation_handwrite":
        if not ciyu_entries:
            return {"error": "该课/单元暂无词语数据"}
        eligible = [
            w for w in ciyu_entries
            if len(w["word"]) >= 2
            and (w["word"] in HOMOPHONE_HINTS
                 or not _pinyin_has_other_word(w["pinyin"], w["word"]))
        ]
        if not eligible:
            eligible = ciyu_entries
        word_entry = random.choice(eligible)
        q = {
            "mode": mode,
            "question": word_entry["pinyin"],
            "answer": word_entry["word"],
        }
        if _pinyin_has_other_word(word_entry["pinyin"], word_entry["word"]):
            hint = HOMOPHONE_HINTS.get(word_entry["word"])
            if hint:
                q["homophone_hint"] = hint
        return q

    # For char modes, convert 识字 entries to CHARACTERS-compatible format
    if not shizi_entries:
        return {"error": "该课/单元暂无识字数据"}

    # Build char_list with {char, pinyin, words} format
    char_list = []
    for e in shizi_entries:
        char_list.append({
            "char": e["word"], "pinyin": e["pinyin"],
            "words": _char_word_examples(e["word"], e["pinyin"], grade),
        })

    if len(char_list) < 2:
        return {"error": "该课字数太少，无法出题"}

    correct = random.choice(char_list)
    # Use full grade characters for distractors so there are enough options
    all_chars = CHARACTERS.get(grade, [])
    # Also include other lesson chars as distractor pool
    distractor_pool = [c for c in char_list if c["char"] != correct["char"]]
    distractor_pool += [c for c in all_chars if c["char"] != correct["char"]]

    if mode == "char_to_pinyin":
        distractors = _pick_distractors(correct, distractor_pool, key="pinyin")
        options = [correct["pinyin"]] + [d["pinyin"] for d in distractors]
        random.shuffle(options)
        q = {
            "mode": mode, "question": correct["char"], "options": options,
            "correct_index": options.index(correct["pinyin"]),
            "answer": correct["pinyin"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }
        if correct["char"] in MULTI_PINYIN:
            ln0 = lessons[0] if lessons else 0
            cw = _find_context_word(correct["char"], correct["pinyin"], grade, ln0)
            if cw:
                q["context_word"] = cw
        return q

    if mode == "pinyin_to_char":
        distractors = _pick_distractors(correct, distractor_pool, key="char")
        options = [correct["char"]] + [d["char"] for d in distractors]
        random.shuffle(options)
        return {
            "mode": mode, "question": correct["pinyin"], "options": options,
            "correct_index": options.index(correct["char"]),
            "answer": correct["char"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }

    if mode == "listen_to_char":
        distractors = _pick_distractors(correct, distractor_pool, key="char",
                                        exclude_homophones=True)
        options = [correct["char"]] + [d["char"] for d in distractors]
        random.shuffle(options)
        return {
            "mode": mode, "question": correct["char"],
            "question_pinyin": correct["pinyin"],
            "options": options, "correct_index": options.index(correct["char"]),
            "answer": correct["char"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }

    if mode == "read_aloud":
        q = {
            "mode": mode,
            "question": correct["char"],
            "answer": correct["pinyin"],
            "answer_char": correct["char"],
            "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
        }
        if correct["char"] in MULTI_PINYIN:
            ln0 = lessons[0] if lessons else 0
            cw = _find_context_word(correct["char"], correct["pinyin"], grade, ln0)
            if cw:
                q["context_word"] = cw
        return q

    return {"error": f"Unknown mode: {mode}"}


@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/register", methods=["POST"])
def register():
    if _rate_limited(f"register:{request.remote_addr}", 5, 60):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429

    data = request.get_json()
    username = (data.get("username") or "").strip()
    password = data.get("password") or ""

    if not username or not password:
        return jsonify({"error": "用户名和密码不能为空"}), 400
    if len(username) > 20:
        return jsonify({"error": "用户名不能超过20个字符"}), 400
    if len(password) < 4:
        return jsonify({"error": "密码至少需要4个字符"}), 400

    db = get_db()
    existing = db.execute("SELECT id FROM users WHERE username = %s", (username,)).fetchone()
    if existing:
        return jsonify({"error": "用户名已存在"}), 409

    pw_hash = hash_password(password)
    cursor = db.execute("INSERT INTO users (username, password_hash) VALUES (%s, %s) RETURNING id", (username, pw_hash))
    user_id = cursor.fetchone()["id"]
    db.commit()
    session.clear()
    session.permanent = True
    session["user_id"] = user_id
    session["username"] = username
    return jsonify({"username": username, "csrf_token": _generate_csrf_token()})


@app.route("/api/login", methods=["POST"])
def login():
    if _rate_limited(f"login:{request.remote_addr}", 10, 60):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429

    data = request.get_json()
    username = (data.get("username") or "").strip()
    password = data.get("password") or ""

    if not username or not password:
        return jsonify({"error": "用户名和密码不能为空"}), 400

    db = get_db()
    user = db.execute("SELECT * FROM users WHERE username = %s", (username,)).fetchone()
    if not user or not verify_password(password, user["password_hash"]):
        return jsonify({"error": "用户名或密码错误"}), 401

    _migrate_password_if_needed(db, user["id"], password, user["password_hash"])
    db.commit()

    session.clear()
    session.permanent = True
    session["user_id"] = user["id"]
    session["username"] = username
    return jsonify({"username": username, "csrf_token": _generate_csrf_token()})


@app.route("/api/logout", methods=["POST"])
def logout():
    session.clear()
    return jsonify({"ok": True})


@app.route("/api/me")
def me():
    if "user_id" not in session:
        return jsonify({"logged_in": False})
    return jsonify({"logged_in": True, "username": session["username"]})


# ---------------------------------------------------------------------------
# Parental control
# ---------------------------------------------------------------------------

def _current_parent_user_id():
    """Return the child user_id this session is acting as a parent for, or None."""
    return session.get("parent_user_id")


def _active_homework_plans(db, user_id):
    """Return at most one active homework plan per mode for a user."""
    rows = db.execute(
        """SELECT * FROM homework_plans
           WHERE user_id = %s AND active = 1
           ORDER BY CASE mode
                      WHEN 'by_lesson' THEN 0
                      WHEN 'book_review' THEN 1
                      ELSE 2
                    END,
                    id DESC""",
        (user_id,),
    ).fetchall()
    plans = []
    seen_modes = set()
    for row in rows:
        mode = row["mode"] if "mode" in row.keys() else "by_lesson"
        if mode in seen_modes:
            continue
        seen_modes.add(mode)
        plans.append(row)
    return plans


def _homework_plan_info(plan):
    rec_grade = plan["recognition_grade"] or plan["grade"]
    wrt_grade = plan["writing_grade"] or plan["grade"]
    p_mode = plan["mode"] if "mode" in plan.keys() else "by_lesson"
    if p_mode == "book_review":
        rec_total = BOOK_REVIEW_DAYS
        wrt_total = BOOK_REVIEW_DAYS
    else:
        rec_total = len(HOMEWORK_LESSONS.get(rec_grade, {}))
        wrt_total = len(HOMEWORK_LESSONS.get(wrt_grade, {}))
    return {
        "id": plan["id"],
        "grade": plan["grade"],
        "grade_short": grade_short_name(plan["grade"]),
        "recognition_grade": rec_grade,
        "writing_grade": wrt_grade,
        "recognition_lesson": plan["recognition_lesson"],
        "writing_lesson": plan["writing_lesson"],
        "rec_total_lessons": rec_total,
        "wrt_total_lessons": wrt_total,
        "total_lessons": max(rec_total, wrt_total),
        "mode": p_mode,
        "active": plan["active"] if "active" in plan.keys() else 1,
    }


@app.route("/api/user/set_parent_password", methods=["POST"])
def set_parent_password():
    """Deprecated: parent password setup now belongs on the parent page."""
    return jsonify({"error": "请在家长登录页面设置或修改家长密码"}), 400


@app.route("/api/user/parent_status")
def user_parent_status():
    """Tell the logged-in user whether a parent password is set."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    row = db.execute(
        "SELECT parent_password_hash FROM users WHERE id = %s",
        (session["user_id"],),
    ).fetchone()
    return jsonify({"has_parent_password": bool(row and row["parent_password_hash"])})


# ---------------------------------------------------------------------------
# Password change & email-based recovery
# ---------------------------------------------------------------------------

@app.route("/api/user/security_status")
def user_security_status():
    """Return the logged-in user's recovery email status + parent password flag."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    row = db.execute(
        "SELECT email, parent_password_hash FROM users WHERE id = %s",
        (session["user_id"],),
    ).fetchone()
    if not row:
        return jsonify({"error": "用户不存在"}), 404
    return jsonify({
        "email": row["email"] or "",
        "email_masked": _mask_email(row["email"] or ""),
        "has_email": bool(row["email"]),
        "has_parent_password": bool(row["parent_password_hash"]),
    })


@app.route("/api/user/set_email", methods=["POST"])
def user_set_email():
    """Set or update the logged-in user's recovery email. Requires current login password."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    data = request.get_json(force=True, silent=True) or {}
    email = (data.get("email") or "").strip()
    current_pw = data.get("current_password") or ""
    if not _looks_like_email(email):
        return jsonify({"error": "请输入有效的邮箱地址"}), 400
    db = get_db()
    row = db.execute(
        "SELECT password_hash FROM users WHERE id = %s",
        (session["user_id"],),
    ).fetchone()
    if not row or not verify_password(current_pw, row["password_hash"]):
        return jsonify({"error": "当前登录密码错误"}), 403
    db.execute("UPDATE users SET email = %s WHERE id = %s", (email, session["user_id"]))
    db.commit()
    return jsonify({"ok": True, "email_masked": _mask_email(email)})


@app.route("/api/user/send_reset_code", methods=["POST"])
def user_send_reset_code():
    """Send a reset code to the user's recovery email.

    For "login" target the user does NOT need to be logged in (this is the
    forgot-password flow); username + email-on-record must match.
    """
    if _rate_limited(f"send_reset_code:{request.remote_addr}", 5, 300):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429
    data = request.get_json(force=True, silent=True) or {}
    target = data.get("target") or ""
    if target != "login":
        return jsonify({"error": "无效请求"}), 400

    db = get_db()
    username = (data.get("username") or "").strip()
    if not username:
        return jsonify({"error": "请输入用户名"}), 400
    user = db.execute(
        "SELECT id, username, email FROM users WHERE username = %s",
        (username,),
    ).fetchone()

    if not user:
        # Don't reveal whether the username exists.
        return jsonify({"ok": True, "sent": False, "message": "如果该账号存在并设置了找回邮箱，验证码已发送"})

    if not user["email"]:
        return jsonify({"error": "该账号没有设置找回邮箱，无法通过邮件重置；请联系管理员"}), 400

    user_dict = dict(user)
    ok, err = _store_and_send_reset_code(db, user_dict, target)
    if not ok:
        return jsonify({"error": err}), 500
    return jsonify({"ok": True, "sent": True, "email_masked": _mask_email(user["email"])})


@app.route("/api/user/change_password", methods=["POST"])
def user_change_password():
    """Change the user's login password.

    Body fields:
      target: 'login'
      mode:   'current' (verify with current login password) or 'code' (verify with email reset code)
      current_password / code: depending on mode
      username: required only for forgot-login (mode=code, target=login, no session)
      new_password: the new login password (4+ chars)
    """
    if _rate_limited(f"change_pw:{request.remote_addr}", 10, 300):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429
    data = request.get_json(force=True, silent=True) or {}
    target = data.get("target") or ""
    mode = data.get("mode") or ""
    new_pw = data.get("new_password") or ""
    if target != "login" or mode not in ("current", "code"):
        return jsonify({"error": "无效请求"}), 400

    db = get_db()
    user = None

    if mode == "code" and target == "login" and "user_id" not in session:
        # Forgot-login flow: username + code identifies the account.
        username = (data.get("username") or "").strip()
        if not username:
            return jsonify({"error": "请输入用户名"}), 400
        user = db.execute("SELECT * FROM users WHERE username = %s", (username,)).fetchone()
    else:
        if "user_id" not in session:
            return jsonify({"error": "未登录"}), 401
        user = db.execute("SELECT * FROM users WHERE id = %s", (session["user_id"],)).fetchone()

    if not user:
        return jsonify({"error": "用户名或验证码错误"}), 401

    if mode == "current":
        if not verify_password(data.get("current_password") or "", user["password_hash"]):
            return jsonify({"error": "当前登录密码错误"}), 403
    else:  # mode == "code"
        if not _consume_reset_code(db, user["id"], target, data.get("code") or ""):
            return jsonify({"error": "验证码无效或已过期"}), 403

    if len(new_pw) < 4:
        return jsonify({"error": "新密码至少需要4个字符"}), 400
    db.execute("UPDATE users SET password_hash = %s WHERE id = %s", (hash_password(new_pw), user["id"]))
    db.commit()
    # If the user wasn't logged in (forgot-password flow), establish a
    # fresh session so they're signed in with the new password.
    if "user_id" not in session:
        session.clear()
        session.permanent = True
        session["user_id"] = user["id"]
        session["username"] = user["username"]
    return jsonify({"ok": True})


@app.route("/api/parent/login", methods=["POST"])
def parent_login():
    if _rate_limited(f"parent_login:{request.remote_addr}", 10, 60):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429
    data = request.get_json(force=True, silent=True) or {}
    username = (data.get("username") or "").strip()
    password = data.get("password") or ""
    if not username or not password:
        return jsonify({"error": "用户名和家长密码不能为空"}), 400
    db = get_db()
    row = db.execute(
        "SELECT id, username, parent_password_hash FROM users WHERE username = %s",
        (username,),
    ).fetchone()
    if not row or not row["parent_password_hash"]:
        return jsonify({"error": "该用户未设置家长密码"}), 401
    if not verify_password(password, row["parent_password_hash"]):
        return jsonify({"error": "家长密码错误"}), 401

    # Parent session is separate from the child's login session — clear
    # both sides to avoid any confusion between the two roles.
    session.clear()
    session.permanent = True
    session["parent_user_id"] = row["id"]
    session["parent_child_username"] = row["username"]
    return jsonify({
        "ok": True,
        "child_id": row["id"],
        "child_username": row["username"],
        "csrf_token": _generate_csrf_token(),
    })


@app.route("/api/parent/set_password", methods=["POST"])
def parent_set_password():
    """Set or reset the parent password from the parent page.

    This verifies the child account's login password, so the parent password
    setup no longer depends on the child already being logged in elsewhere.
    """
    if _rate_limited(f"parent_set_password:{request.remote_addr}", 10, 300):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429

    data = request.get_json(force=True, silent=True) or {}
    username = (data.get("username") or "").strip()
    child_password = data.get("child_password") or ""
    new_pw = data.get("new_password") or ""

    if not username or not child_password:
        return jsonify({"error": "请输入孩子用户名和孩子账号登录密码"}), 400
    if len(new_pw) < 4:
        return jsonify({"error": "家长密码至少需要4个字符"}), 400

    db = get_db()
    user = db.execute("SELECT * FROM users WHERE username = %s", (username,)).fetchone()
    if not user or not verify_password(child_password, user["password_hash"]):
        return jsonify({"error": "孩子用户名或登录密码错误"}), 401

    _migrate_password_if_needed(db, user["id"], child_password, user["password_hash"])
    db.execute(
        "UPDATE users SET parent_password_hash = %s WHERE id = %s",
        (hash_password(new_pw), user["id"]),
    )
    db.commit()
    return jsonify({"ok": True, "child_username": user["username"]})


@app.route("/api/parent/change_password", methods=["POST"])
def parent_change_password():
    """Change or clear the parent password while logged in as parent."""
    if _rate_limited(f"parent_change_password:{request.remote_addr}", 10, 300):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429

    uid = _current_parent_user_id()
    if not uid:
        return jsonify({"error": "需要家长登录"}), 401

    data = request.get_json(force=True, silent=True) or {}
    current_pw = data.get("current_parent_password") or ""
    new_pw = data.get("new_password") or ""
    if not current_pw:
        return jsonify({"error": "请输入当前家长密码"}), 400

    db = get_db()
    user = db.execute(
        "SELECT id, parent_password_hash FROM users WHERE id = %s",
        (uid,),
    ).fetchone()
    if not user or not user["parent_password_hash"]:
        return jsonify({"error": "该用户未设置家长密码"}), 400
    if not verify_password(current_pw, user["parent_password_hash"]):
        return jsonify({"error": "当前家长密码错误"}), 403

    if new_pw == "":
        db.execute("UPDATE users SET parent_password_hash = '' WHERE id = %s", (uid,))
        db.commit()
        session.clear()
        return jsonify({"ok": True, "cleared": True})

    if len(new_pw) < 4:
        return jsonify({"error": "家长密码至少需要4个字符"}), 400

    db.execute(
        "UPDATE users SET parent_password_hash = %s WHERE id = %s",
        (hash_password(new_pw), uid),
    )
    db.commit()
    return jsonify({"ok": True})


@app.route("/api/parent/logout", methods=["POST"])
def parent_logout():
    session.clear()
    return jsonify({"ok": True})


@app.route("/api/parent/me")
def parent_me():
    uid = _current_parent_user_id()
    if not uid:
        return jsonify({"logged_in": False})
    return jsonify({
        "logged_in": True,
        "child_id": uid,
        "child_username": session.get("parent_child_username", ""),
    })


def _game_time_records(db, user_id, limit=50):
    exchanges = db.execute(
        """SELECT exchange_date, coins, minutes
           FROM exchange_records
           WHERE user_id = %s
           ORDER BY exchange_date DESC, created_at DESC, id DESC
           LIMIT %s""",
        (user_id, limit),
    ).fetchall()
    usage = db.execute(
        """SELECT usage_date, minutes, purpose
           FROM game_usage_records
           WHERE user_id = %s
           ORDER BY usage_date DESC, created_at DESC, id DESC
           LIMIT %s""",
        (user_id, limit),
    ).fetchall()
    return [dict(r) for r in exchanges], [dict(r) for r in usage]


@app.route("/api/parent/overview")
def parent_overview():
    uid = _current_parent_user_id()
    if not uid:
        return jsonify({"error": "需要家长登录"}), 401
    db = get_db()
    user = db.execute(
        "SELECT id, username, coins, game_minutes, created_at FROM users WHERE id = %s",
        (uid,),
    ).fetchone()
    if not user:
        return jsonify({"error": "用户不存在"}), 404

    plan_infos = [_homework_plan_info(p) for p in _active_homework_plans(db, uid)]
    plan_dict = plan_infos[0] if plan_infos else None

    today = date.today().isoformat()
    today_assignments = db.execute(
        """SELECT id, type, grade, lesson_num, mode, status,
                  total_questions, correct_answers, time_spent
           FROM daily_assignments
           WHERE user_id = %s AND date = %s
           ORDER BY CASE mode
                      WHEN 'by_lesson' THEN 0
                      WHEN 'book_review' THEN 1
                      ELSE 2
                    END,
                    type, id""",
        (uid, today),
    ).fetchall()

    recent_assignments = db.execute(
        """SELECT date, type, grade, lesson_num, mode, status,
                  total_questions, correct_answers, time_spent
           FROM daily_assignments
           WHERE user_id = %s AND date >= %s
           ORDER BY date DESC,
                    CASE mode
                      WHEN 'by_lesson' THEN 0
                      WHEN 'book_review' THEN 1
                      ELSE 2
                    END,
                    type, id""",
        (uid, (date.today() - timedelta(days=14)).isoformat()),
    ).fetchall()

    wrong_count_row = db.execute(
        "SELECT COUNT(*) as cnt FROM wrong_answers WHERE user_id = %s",
        (uid,),
    ).fetchone()
    mastered_count_row = db.execute(
        "SELECT COUNT(*) as cnt FROM wrong_answer_events WHERE user_id = %s AND mastered = 1",
        (uid,),
    ).fetchone()

    coin_totals = db.execute(
        """SELECT source,
                  COALESCE(SUM(CASE WHEN amount > 0 THEN amount ELSE 0 END), 0) as earned,
                  COALESCE(SUM(CASE WHEN amount < 0 THEN -amount ELSE 0 END), 0) as spent
           FROM coin_transactions WHERE user_id = %s GROUP BY source""",
        (uid,),
    ).fetchall()
    exchange_recent, game_usage_recent = _game_time_records(db, uid, limit=50)

    return jsonify({
        "user": dict(user),
        "plan": plan_dict,
        "plans": plan_infos,
        "today_assignments": [dict(r) for r in today_assignments],
        "recent_assignments": [dict(r) for r in recent_assignments],
        "wrong_count": wrong_count_row["cnt"] if wrong_count_row else 0,
        "mastered_count": mastered_count_row["cnt"] if mastered_count_row else 0,
        "coin_totals": [dict(r) for r in coin_totals],
        "exchange_recent": exchange_recent,
        "game_usage_recent": game_usage_recent,
        "grades": list(CHARACTERS.keys()),
        "lesson_counts": lesson_counts_by_grade(),
        "book_review_days": BOOK_REVIEW_DAYS,
    })


@app.route("/api/parent/homework/plan", methods=["POST"])
def parent_set_plan():
    """Set/update the child's homework plan. Mirrors the admin endpoint but
    scoped to the parent's own child."""
    uid = _current_parent_user_id()
    if not uid:
        return jsonify({"error": "需要家长登录"}), 401

    data = request.get_json(force=True, silent=True) or {}
    grade = data.get("grade", "")
    rec_grade = data.get("recognition_grade") or grade
    wrt_grade = data.get("writing_grade") or grade
    rec_lesson = int(data.get("recognition_lesson", 1) or 1)
    wrt_lesson = int(data.get("writing_lesson", 1) or 1)
    mode = data.get("mode", "by_lesson")
    if mode not in ("by_lesson", "book_review"):
        mode = "by_lesson"
    if grade not in CHARACTERS:
        return jsonify({"error": "年级无效"}), 400
    if mode == "book_review":
        if not (1 <= rec_lesson <= BOOK_REVIEW_DAYS and 1 <= wrt_lesson <= BOOK_REVIEW_DAYS):
            return jsonify({"error": f"分册复习天数需在 1-{BOOK_REVIEW_DAYS} 之间"}), 400
    else:
        total_lessons = len(HOMEWORK_LESSONS.get(grade, {}))
        if not (1 <= rec_lesson <= total_lessons and 1 <= wrt_lesson <= total_lessons):
            return jsonify({"error": f"{grade} 共 {total_lessons} 课，课号需在 1-{total_lessons} 之间"}), 400

    db = get_db()
    # Keep one active plan per mode, so by-lesson homework and book review
    # can coexist without overwriting each other.
    db.execute("UPDATE homework_plans SET active = 0 WHERE user_id = %s AND mode = %s", (uid, mode))
    # Insert new plan
    db.execute(
        """INSERT INTO homework_plans
                (user_id, grade, recognition_grade, writing_grade,
                 recognition_lesson, writing_lesson, mode, active)
           VALUES (%s, %s, %s, %s, %s, %s, %s, 1)""",
        (uid, grade, rec_grade, wrt_grade, rec_lesson, wrt_lesson, mode),
    )
    # Clear today's pending assignments so new plan takes effect immediately
    today = date.today().isoformat()
    db.execute(
        "DELETE FROM daily_assignments WHERE user_id = %s AND date = %s AND status = 'pending' AND mode = %s",
        (uid, today, mode),
    )
    db.commit()
    return jsonify({"ok": True})


@app.route("/parent")
def parent_page():
    return render_template(
        "parent.html",
        grades=list(CHARACTERS.keys()),
        lesson_counts=lesson_counts_by_grade(),
        book_review_days=BOOK_REVIEW_DAYS,
    )


def _smtp_config():
    """Return (host, port, user, pwd, sender, use_ssl) or None if SMTP isn't configured."""
    host = os.environ.get("SMTP_HOST", "").strip()
    user = os.environ.get("SMTP_USER", "").strip()
    pwd = os.environ.get("SMTP_PASSWORD", "").strip()
    if not (host and user and pwd):
        return None
    port = int(os.environ.get("SMTP_PORT", "587"))
    sender = os.environ.get("SMTP_FROM", user).strip() or user
    use_ssl = os.environ.get("SMTP_USE_SSL", "").strip() in ("1", "true", "True")
    return (host, port, user, pwd, sender, use_ssl)


def _send_email(to_email: str, subject: str, body: str, reply_to: str = "", attachments=None) -> tuple[bool, str]:
    """Send a plain-text email. Returns (ok, error)."""
    cfg = _smtp_config()
    if cfg is None:
        return False, "smtp_not_configured"
    host, port, user, pwd, sender, use_ssl = cfg
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = to_email
    if reply_to:
        msg["Reply-To"] = reply_to
    msg.set_content(body)
    for att in attachments or []:
        content = att.get("content") or b""
        mime = att.get("mime") or "application/octet-stream"
        filename = att.get("filename") or "attachment"
        maintype, _, subtype = mime.partition("/")
        msg.add_attachment(content, maintype=maintype or "application", subtype=subtype or "octet-stream", filename=filename)
    try:
        if use_ssl:
            with smtplib.SMTP_SSL(host, port, timeout=10) as s:
                s.login(user, pwd)
                s.send_message(msg)
        else:
            with smtplib.SMTP(host, port, timeout=10) as s:
                s.ehlo()
                s.starttls()
                s.login(user, pwd)
                s.send_message(msg)
        return True, ""
    except Exception as e:
        return False, str(e)[:500]


def _send_contact_email(from_name: str, reply_email: str, subject: str, message: str, image_attachment=None) -> tuple[bool, str]:
    """Send a contact-us message to ADMIN_CONTACT_EMAIL via SMTP."""
    attachments = [image_attachment] if image_attachment else None
    body = "\n".join([
        f"来自用户: {from_name or '(匿名)'}",
        f"回复邮箱: {reply_email or '(未填写)'}",
        f"图片附件: {image_attachment['filename']}" if image_attachment else "图片附件: 无",
        "",
        message or "",
    ])
    return _send_email(
        ADMIN_CONTACT_EMAIL,
        f"[汉字游戏 留言] {subject or '(无主题)'}",
        body,
        reply_to=reply_email,
        attachments=attachments,
    )


def _parse_contact_image(image_data):
    """Validate and decode one contact-us image attachment."""
    if not image_data:
        return None, ""
    if not isinstance(image_data, dict):
        return None, "图片数据格式不正确"

    name = os.path.basename((image_data.get("name") or "bug-report-image").strip())[:120]
    mime = (image_data.get("mime") or "").strip().lower()
    raw_data = (image_data.get("data") or "").strip()
    if not raw_data:
        return None, ""

    if raw_data.startswith("data:"):
        header, _, raw_data = raw_data.partition(",")
        if ";base64" not in header:
            return None, "图片格式不正确"
        if not mime:
            mime = header[5:].split(";", 1)[0].lower()

    allowed = {"image/png", "image/jpeg", "image/gif", "image/webp"}
    if mime not in allowed:
        return None, "图片只能是 PNG、JPG、GIF 或 WebP 格式"

    try:
        content = base64.b64decode(raw_data, validate=True)
    except Exception:
        return None, "图片读取失败，请重新选择"
    if len(content) > 5 * 1024 * 1024:
        return None, "图片不能超过 5MB"
    if not name:
        ext = {"image/png": "png", "image/jpeg": "jpg", "image/gif": "gif", "image/webp": "webp"}[mime]
        name = f"bug-report.{ext}"

    return {
        "filename": name,
        "mime": mime,
        "data": base64.b64encode(content).decode("ascii"),
        "content": content,
    }, ""


def _mask_email(email: str) -> str:
    """Mask an email for display: 'fcyucn@gmail.com' -> 'f***n@gmail.com'."""
    if not email or "@" not in email:
        return ""
    local, _, domain = email.partition("@")
    if len(local) <= 2:
        masked_local = local[0] + "*"
    else:
        masked_local = local[0] + "*" * (len(local) - 2) + local[-1]
    return f"{masked_local}@{domain}"


def _looks_like_email(s: str) -> bool:
    s = (s or "").strip()
    if not s or "@" not in s or len(s) > 200:
        return False
    local, _, domain = s.partition("@")
    if not local or not domain or "." not in domain:
        return False
    return True


def _generate_reset_code() -> str:
    """Generate a 6-digit numeric code."""
    return f"{random.randint(0, 999999):06d}"


def _hash_reset_code(code: str) -> str:
    return hashlib.sha256(code.encode()).hexdigest()


def _store_and_send_reset_code(db, user_row, target: str) -> tuple[bool, str]:
    """Generate a reset code, store its hash, email it to the user. Returns (ok, error_msg).

    On smtp_not_configured we still rotate the code so old ones don't outlive
    the request, but the caller should surface a friendly error.
    """
    if not user_row.get("email"):
        return False, "用户没有设置找回邮箱"
    code = _generate_reset_code()
    expires_at = datetime.utcnow() + timedelta(minutes=15)
    # Invalidate any prior unused codes for this target.
    db.execute(
        "UPDATE password_reset_codes SET used = 1 WHERE user_id = %s AND target = %s AND used = 0",
        (user_row["id"], target),
    )
    db.execute(
        "INSERT INTO password_reset_codes (user_id, target, code_hash, expires_at) VALUES (%s, %s, %s, %s)",
        (user_row["id"], target, _hash_reset_code(code), expires_at),
    )
    db.commit()
    label = "登录密码" if target == "login" else "家长密码"
    body = (
        f"你正在为 {user_row['username']} 重置「{label}」。\n\n"
        f"验证码: {code}\n"
        f"有效期: 15 分钟\n\n"
        f"如果不是你本人操作，请忽略此邮件。"
    )
    ok, err = _send_email(user_row["email"], f"[汉字小达人] {label}重置验证码", body)
    if not ok:
        return False, "邮件发送失败，请稍后再试" if err == "smtp_not_configured" else f"邮件发送失败: {err}"
    return True, ""


def _consume_reset_code(db, user_id: int, target: str, code: str) -> bool:
    """Verify a reset code; mark used on success. Returns True if valid."""
    if not code or len(code) != 6 or not code.isdigit():
        return False
    row = db.execute(
        """SELECT id FROM password_reset_codes
           WHERE user_id = %s AND target = %s AND used = 0
                 AND code_hash = %s AND expires_at > %s
           ORDER BY id DESC LIMIT 1""",
        (user_id, target, _hash_reset_code(code), datetime.utcnow()),
    ).fetchone()
    if not row:
        return False
    db.execute("UPDATE password_reset_codes SET used = 1 WHERE id = %s", (row["id"],))
    return True


@app.route("/contact")
def contact_page():
    return render_template(
        "contact.html",
        admin_email=ADMIN_CONTACT_EMAIL,
        username=session.get("username", ""),
    )


@app.route("/api/contact", methods=["POST"])
def contact_api():
    """Accept a contact-us message. Non-logged-in users can submit too."""
    if _rate_limited(f"contact:{request.remote_addr}", 5, 300):
        return jsonify({"error": "提交过于频繁，请稍后再试"}), 429

    data = request.get_json(force=True, silent=True) or {}
    subject = (data.get("subject") or "").strip()[:200]
    message = (data.get("message") or "").strip()
    reply_email = (data.get("reply_email") or "").strip()[:200]
    if not message:
        return jsonify({"error": "请填写留言内容"}), 400
    if len(message) > 4000:
        return jsonify({"error": "留言过长（4000字以内）"}), 400

    user_id = session.get("user_id")
    username = session.get("username", "") or (data.get("username") or "").strip()[:50]
    image_attachment, image_error = _parse_contact_image(data.get("image"))
    if image_error:
        return jsonify({"error": image_error}), 400

    # Send email first — capture result so we can store alongside the message.
    ok, err = _send_contact_email(username, reply_email, subject, message, image_attachment=image_attachment)

    db = get_db()
    db.execute(
        """INSERT INTO contact_messages
                (user_id, username, reply_email, subject, message,
                 image_name, image_mime, image_data, email_sent, email_error)
           VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)""",
        (
            user_id, username, reply_email, subject, message,
            image_attachment["filename"] if image_attachment else "",
            image_attachment["mime"] if image_attachment else "",
            image_attachment["data"] if image_attachment else "",
            1 if ok else 0, "" if ok else err,
        ),
    )
    db.commit()

    return jsonify({
        "ok": True,
        "email_sent": ok,
        "admin_email": ADMIN_CONTACT_EMAIL,
    })


@app.route("/api/admin/messages")
def admin_messages():
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403
    db = get_db()
    rows = db.execute(
        """SELECT id, user_id, username, reply_email, subject, message,
                  image_name, image_mime, image_data,
                  email_sent, email_error, created_at
           FROM contact_messages ORDER BY created_at DESC LIMIT 100"""
    ).fetchall()
    return jsonify({"messages": [dict(r) for r in rows]})


@app.route("/api/scores", methods=["GET", "POST"])
def scores_api():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    if request.method == "POST":
        data = request.get_json(force=True, silent=True)
        if not data:
            return jsonify({"error": "无效的请求数据"}), 400
        grade = data.get("grade", "")
        mode = data.get("mode", "")
        score = data.get("score", 0)
        combo_max = data.get("combo_max", 0)
        total_questions = data.get("total_questions", 0)
        correct_answers = data.get("correct_answers", 0)

        if not isinstance(score, int) or score < 0:
            return jsonify({"error": "无效分数"}), 400
        if total_questions <= 0:
            return jsonify({"ok": True})

        db = get_db()
        score_row = db.execute(
            """INSERT INTO scores
               (user_id, grade, mode, score, combo_max, total_questions, correct_answers)
               VALUES (%s, %s, %s, %s, %s, %s, %s)
               RETURNING id, DATE(created_at) as source_date, created_at""",
            (session["user_id"], grade, mode, score, combo_max, total_questions, correct_answers),
        ).fetchone()
        wrong_items = data.get("wrong_items", [])
        if isinstance(wrong_items, list) and score_row:
            source_label = _source_label("game", grade=grade, mode=mode)
            for idx, item in enumerate(wrong_items):
                payload = _wrong_item_payload(item, fallback_grade=grade, fallback_mode=mode)
                event_key = f"score:{score_row['id']}:{idx}:{payload['character']}:{payload['mode']}"
                _insert_wrong_event(
                    db,
                    session["user_id"],
                    item,
                    source="game",
                    source_id=score_row["id"],
                    source_date=str(score_row["source_date"]),
                    source_label=source_label,
                    event_key=event_key,
                    fallback_grade=grade,
                    fallback_mode=mode,
                    created_at=score_row["created_at"],
                )
        db.commit()
        return jsonify({"ok": True})

    db = get_db()
    # Combine game scores and homework scores by date
    game_rows = db.execute(
        """SELECT DATE(created_at) as date,
                  SUM(total_questions) as total_questions,
                  SUM(correct_answers) as correct_answers,
                  SUM(score) as score
           FROM scores WHERE user_id = %s
           GROUP BY DATE(created_at)""",
        (session["user_id"],),
    ).fetchall()
    hw_rows = db.execute(
        """SELECT date,
                  SUM(total_questions) as total_questions,
                  SUM(correct_answers) as correct_answers,
                  0 as score
           FROM daily_assignments WHERE user_id = %s AND status = 'completed'
           GROUP BY date""",
        (session["user_id"],),
    ).fetchall()

    # Merge by date
    merged = {}
    for r in game_rows:
        d = str(r["date"])
        merged[d] = {"date": r["date"], "total_questions": r["total_questions"], "correct_answers": r["correct_answers"], "score": r["score"], "source": "游戏"}
    for r in hw_rows:
        d = str(r["date"])
        if d in merged:
            merged[d]["total_questions"] += r["total_questions"]
            merged[d]["correct_answers"] += r["correct_answers"]
            merged[d]["source"] = "游戏+作业"
        else:
            merged[d] = {"date": r["date"], "total_questions": r["total_questions"], "correct_answers": r["correct_answers"], "score": 0, "source": "作业"}

    wrong_event_rows = db.execute(
        """SELECT id, character, pinyin, words, grade, mode, source, source_id,
                  source_date, source_label, question, correct_answer,
                  user_answer, review_count, mastered, mastered_at, created_at
           FROM wrong_answer_events
           WHERE user_id = %s
           ORDER BY source_date DESC, created_at DESC, id DESC""",
        (session["user_id"],),
    ).fetchall()
    wrong_book = [dict(r) for r in wrong_event_rows]
    wrong_events_by_date = {}
    for item in wrong_book:
        wrong_events_by_date.setdefault(str(item["source_date"]), []).append(item)

    scores = []
    for d in sorted(merged.keys(), reverse=True)[:60]:
        entry = merged[d]
        events = wrong_events_by_date.get(d, [])
        diff = max(0, (entry.get("total_questions") or 0) - (entry.get("correct_answers") or 0))
        entry["wrong_items"] = events
        entry["traceable_wrong_count"] = len(events)
        entry["untraced_wrong_count"] = max(0, diff - len(events))
        entry["wrong_count"] = len(events) + entry["untraced_wrong_count"]
        entry["wrong_chars"] = [e["character"] for e in events]
        scores.append(entry)
    return jsonify({"scores": scores, "wrong_book": wrong_book})


@app.route("/history")
def history_page():
    if "user_id" not in session:
        return redirect(url_for("index"))
    return render_template("history.html", username=session["username"])


@app.route("/api/handwriting", methods=["POST"])
def handwriting():
    data = request.get_json()
    payload = json.dumps({
        "input_type": 0,
        "requests": [{
            "writing_guide": {"width": data["width"], "height": data["height"]},
            "ink": data["strokes"],
            "language": "zh",
        }],
    }).encode()
    req = urllib.request.Request(
        "https://inputtools.google.com/request?itc=zh-t-i0-handwrit&app=translate",
        data=payload,
        headers={"Content-Type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            result = json.loads(resp.read())
        return jsonify(result)
    except Exception:
        return jsonify({"error": "识别失败"}), 502


@app.route("/api/wrong_answers", methods=["GET", "POST"])
def wrong_answers_api():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    if request.method == "POST":
        data = request.get_json(force=True, silent=True)
        if not data:
            return jsonify({"error": "无效的请求数据"}), 400
        db = get_db()
        words = data.get("words", "")
        if data.get("mode") != "dictation_handwrite":
            words = _recognition_word_hint(
                data.get("character", ""), data.get("pinyin", ""),
                data.get("grade", ""), words,
            )
        db.execute(
            "INSERT INTO wrong_answers (user_id, character, pinyin, words, grade, mode) VALUES (%s, %s, %s, %s, %s, %s)",
            (session["user_id"], data["character"], data["pinyin"], words, data["grade"], data["mode"]),
        )
        db.commit()
        return jsonify({"ok": True})

    date = request.args.get("date")
    review_type = request.args.get("type", "all")
    review_count = request.args.get("review_count", "all")
    db = get_db()
    clauses = ["user_id = %s", "mastered = 0"]
    params = [session["user_id"]]
    if date:
        clauses.append("source_date = %s")
        params.append(date)
    if review_type == "writing":
        clauses.append("(mode = 'dictation_handwrite' OR source_label LIKE %s)")
        params.append("%写字%")
    elif review_type == "recognition":
        clauses.append("NOT (mode = 'dictation_handwrite' OR source_label LIKE %s)")
        params.append("%写字%")
    if review_count in ("0", "1", "2"):
        clauses.append("review_count = %s")
        params.append(int(review_count))

    rows = db.execute(
        f"""SELECT id AS event_id, character, pinyin, words, grade, mode,
                   review_count, source_date AS date, source_label, question,
                   correct_answer
            FROM wrong_answer_events
            WHERE {' AND '.join(clauses)}
            ORDER BY review_count ASC, source_date DESC, created_at DESC, id DESC""",
        tuple(params),
    ).fetchall()
    results = [dict(r) for r in rows]
    for item in results:
        if item.get("mode") != "dictation_handwrite":
            item["words"] = _recognition_word_hint(
                item.get("character", ""), item.get("pinyin", ""),
                item.get("grade", ""), item.get("words", ""),
            )
    return jsonify({"wrong_answers": results})


@app.route("/api/review_question", methods=["POST"])
def review_question():
    """Generate a question for a specific wrong-answer item, using its original mode."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    data = request.get_json()
    character = data.get("character", "")
    pinyin = data.get("pinyin", "")
    words = data.get("words", "")
    grade = data.get("grade", "")
    mode = data.get("mode", "char_to_pinyin")
    question_mode = "dictation_handwrite" if mode == "dictation_handwrite" else "pinyin_typing"
    words = _recognition_word_hint(character, pinyin, grade, words)

    char_list = CHARACTERS.get(grade, [])
    if len(char_list) < 4:
        return jsonify({"error": "年级数据不足"}), 400

    # Build a "correct" entry compatible with _pick_distractors
    correct = {"char": character, "pinyin": pinyin, "words": words.split("、") if words else []}
    # For multi-char questions the single-char CHARACTERS pool has no
    # length-matching candidates. Augment with multi-char 词语 from WORDS
    # (and, failing that, from all grades) so _pick_distractors can satisfy
    # the 字数匹配 constraint.
    if len(character) > 1:
        others = []
        for w in WORDS.get(grade, []):
            if w["word"] != character and len(w["word"]) == len(character):
                others.append({"char": w["word"], "pinyin": w["pinyin"], "words": []})
        if len(others) < 4:
            for g, ws in WORDS.items():
                if g == grade:
                    continue
                for w in ws:
                    if w["word"] != character and len(w["word"]) == len(character):
                        others.append({"char": w["word"], "pinyin": w["pinyin"], "words": []})
    else:
        others = [c for c in char_list if c["char"] != character]

    if question_mode == "pinyin_typing":
        resp = {
            "mode": question_mode, "question": character, "answer": pinyin,
            "word_hint": words, "display_char": character,
            "display_pinyin": pinyin,
        }
        if character in MULTI_PINYIN:
            cw = _find_context_word(character, pinyin, grade, 0)
            if not cw and words:
                cw = words.split("、")[0]
            if cw:
                resp["context_word"] = cw
        return jsonify(resp)

    if question_mode == "pinyin_to_char":
        distractors = _pick_distractors(correct, others, key="char")
        options = [character] + [d["char"] for d in distractors]
        random.shuffle(options)
        return jsonify({
            "mode": question_mode, "question": pinyin, "options": options,
            "correct_index": options.index(character),
            "answer": character, "word_hint": words,
        })

    if question_mode == "listen_to_char":
        distractors = _pick_distractors(correct, others, key="char", exclude_homophones=True)
        options = [character] + [d["char"] for d in distractors]
        random.shuffle(options)
        return jsonify({
            "mode": question_mode, "question": character, "question_pinyin": pinyin,
            "options": options, "correct_index": options.index(character),
            "answer": character, "word_hint": words,
        })

    if question_mode == "dictation_handwrite":
        payload = {"mode": question_mode, "question": pinyin, "answer": character}
        if _pinyin_has_other_word(pinyin, character):
            hint = HOMOPHONE_HINTS.get(character)
            if hint:
                payload["homophone_hint"] = hint
        return jsonify(payload)

    return jsonify({"error": f"Unknown mode: {mode}"}), 400


@app.route("/api/review_done", methods=["POST"])
def review_done():
    """Mark a wrong-book event as reviewed after a correct answer."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    data = request.get_json()
    event_id = data.get("event_id")
    character = data.get("character", "")
    mode = data.get("mode", "")
    db = get_db()

    if event_id:
        row = db.execute(
            "SELECT id, review_count, mastered FROM wrong_answer_events WHERE id = %s AND user_id = %s",
            (event_id, session["user_id"]),
        ).fetchone()
        if not row:
            return jsonify({"error": "错题不存在"}), 404
        next_count = (row["review_count"] or 0) + 1
        if next_count >= 3:
            db.execute(
                """UPDATE wrong_answer_events
                   SET review_count = %s, mastered = 1,
                       mastered_at = COALESCE(mastered_at, CURRENT_TIMESTAMP)
                   WHERE id = %s""",
                (next_count, event_id),
            )
        else:
            db.execute(
                "UPDATE wrong_answer_events SET review_count = %s WHERE id = %s",
                (next_count, event_id),
            )
        db.commit()
        return jsonify({"ok": True, "review_count": next_count, "mastered": next_count >= 3})

    # Backward-compatible path for older open wrong-answer records.
    db.execute(
        "DELETE FROM wrong_answers WHERE user_id = %s AND character = %s AND mode = %s",
        (session["user_id"], character, mode),
    )
    db.commit()

    return jsonify({"ok": True})


@app.route("/api/mastered_words")
def mastered_words_api():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    rows = db.execute(
        """SELECT character, pinyin, words, grade, mode, review_count,
                  source_date AS date, DATE(mastered_at) as mastered_date
           FROM wrong_answer_events
           WHERE user_id = %s AND mastered = 1
           ORDER BY mastered_at DESC, id DESC""",
        (session["user_id"],),
    ).fetchall()
    items = [dict(r) for r in rows]
    for item in items:
        if item.get("mode") != "dictation_handwrite":
            item["words"] = _recognition_word_hint(
                item.get("character", ""), item.get("pinyin", ""),
                item.get("grade", ""), item.get("words", ""),
            )
    return jsonify({"mastered_words": items})


@app.route("/review")
def review_page():
    if "user_id" not in session:
        return redirect(url_for("index"))
    return render_template("review.html", username=session["username"])


@app.route("/api/leaderboard")
def leaderboard():
    mode = request.args.get("mode", "")
    db = get_db()
    if mode:
        rows = db.execute(
            """SELECT u.username,
                      SUM(s.score) as total_score,
                      SUM(s.correct_answers) as total_correct,
                      SUM(s.total_questions) as total_questions
               FROM scores s
               JOIN users u ON s.user_id = u.id
               WHERE s.mode = %s
               GROUP BY s.user_id, u.username
               ORDER BY total_score DESC
               LIMIT 50""",
            (mode,),
        ).fetchall()
    else:
        rows = db.execute(
            """SELECT u.username,
                      SUM(s.score) as total_score,
                      SUM(s.correct_answers) as total_correct,
                      SUM(s.total_questions) as total_questions
               FROM scores s
               JOIN users u ON s.user_id = u.id
               GROUP BY s.user_id, u.username
               ORDER BY total_score DESC
               LIMIT 50""",
        ).fetchall()

    result = []
    for i, r in enumerate(rows):
        d = dict(r)
        d["rank"] = i + 1
        d["accuracy"] = round(d["total_correct"] / d["total_questions"] * 100) if d["total_questions"] > 0 else 0
        result.append(d)

    my_rank = None
    if "user_id" in session:
        for r in result:
            if r["username"] == session["username"]:
                my_rank = r
                break

    return jsonify({"leaderboard": result, "my_rank": my_rank})


@app.route("/api/grades")
def grades():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    grade_list = list(CHARACTERS.keys())
    return jsonify({"grades": grade_list})


@app.route("/api/lessons")
def lessons_api():
    """Return lesson/unit structure for a grade (if available)."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    grade = request.args.get("grade", "")
    grade_lessons = LESSON_DATA.get(grade)
    if not grade_lessons:
        return jsonify({"has_lessons": False})

    units = UNIT_MAP.get(grade, {})
    # Build lesson list with content counts
    lesson_list = []
    for ln in sorted(grade_lessons.keys()):
        ld = grade_lessons[ln]
        lesson_list.append({
            "lesson": ln,
            "shizi_count": len(ld.get("识字", [])),
            "ciyu_count": len(ld.get("词语", [])),
        })

    unit_list = [{"name": name, "lessons": lns}
                 for name, lns in units.items()]

    return jsonify({
        "has_lessons": True,
        "lessons": lesson_list,
        "units": unit_list,
    })


@app.route("/api/question")
def question():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    grade = request.args.get("grade", "一年级上")
    mode = request.args.get("mode", "char_to_pinyin")
    lesson = request.args.get("lesson", "")  # e.g. "5" or "1,2,3,4" for unit
    unit = request.args.get("unit", "")      # e.g. "第一单元"

    if grade not in CHARACTERS:
        return jsonify({"error": f"Unknown grade: {grade}"}), 400

    # Determine lesson list if filtering
    lesson_nums = []
    if unit and grade in UNIT_MAP:
        lesson_nums = UNIT_MAP[grade].get(unit, [])
    elif lesson:
        lesson_nums = [int(x) for x in lesson.split(",") if x.strip().isdigit()]

    if lesson_nums:
        result = _generate_lesson_question(grade, mode, lesson_nums)
    else:
        result = _generate_question(grade, mode)

    if "error" in result:
        return jsonify(result), 400

    return jsonify(result)


# --- Admin routes ---

@app.route("/api/admin/login", methods=["POST"])
def admin_login():
    if _rate_limited(f"admin_login:{request.remote_addr}", 5, 300):
        return jsonify({"error": "请求过于频繁，请稍后再试"}), 429

    data = request.get_json(force=True, silent=True)
    if not data:
        return jsonify({"error": "无效的请求数据"}), 400
    password = data.get("password", "")
    if ADMIN_PASSWORD_HASH:
        if not bcrypt.checkpw(password.encode(), ADMIN_PASSWORD_HASH.encode()):
            return jsonify({"error": "管理员密码错误"}), 401
    elif _legacy_admin_pw:
        if not _hmac.compare_digest(password, _legacy_admin_pw):
            return jsonify({"error": "管理员密码错误"}), 401
    else:
        return jsonify({"error": "管理员认证未配置"}), 500
    session["is_admin"] = True
    return jsonify({"ok": True})


@app.route("/api/admin/logout", methods=["POST"])
def admin_logout():
    session.pop("is_admin", None)
    return jsonify({"ok": True})


@app.route("/api/admin/check")
def admin_check():
    return jsonify({"is_admin": session.get("is_admin", False)})


@app.route("/api/admin/items", methods=["GET"])
def admin_items():
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403
    db = get_db()
    return jsonify({"items": _get_exchange_packages(db)})


@app.route("/api/admin/users")
def admin_users():
    """Return all registered users with summary stats."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    db = get_db()
    users = db.execute(
        """SELECT u.id, u.username, u.coins, u.game_minutes, u.created_at,
                  COALESCE(SUM(s.score), 0) as total_score,
                  COALESCE(SUM(s.total_questions), 0) as total_questions,
                  COALESCE(SUM(s.correct_answers), 0) as correct_answers
           FROM users u
           LEFT JOIN scores s ON u.id = s.user_id
           GROUP BY u.id
           ORDER BY total_score DESC"""
    ).fetchall()

    result = []
    for u in users:
        d = dict(u)
        d["accuracy"] = round(d["correct_answers"] / d["total_questions"] * 100) if d["total_questions"] > 0 else 0
        # Count wrong answers
        wa = db.execute("SELECT COUNT(*) as cnt FROM wrong_answers WHERE user_id = %s", (u["id"],)).fetchone()
        d["wrong_count"] = wa["cnt"]
        # Count mastered
        ma = db.execute("SELECT COUNT(*) as cnt FROM wrong_answer_events WHERE user_id = %s AND mastered = 1", (u["id"],)).fetchone()
        d["mastered_count"] = ma["cnt"]
        result.append(d)

    return jsonify({"users": result})


@app.route("/api/admin/user/<int:user_id>/details")
def admin_user_details(user_id):
    """Return detailed history for a specific user."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    db = get_db()
    user = db.execute("SELECT id, username, coins, game_minutes, created_at FROM users WHERE id = %s", (user_id,)).fetchone()
    if not user:
        return jsonify({"error": "用户不存在"}), 404

    # Score history grouped by date
    scores = db.execute(
        """SELECT DATE(created_at) as date, grade, mode,
                  SUM(total_questions) as total_questions,
                  SUM(correct_answers) as correct_answers,
                  SUM(score) as score
           FROM scores WHERE user_id = %s
           GROUP BY DATE(created_at), grade, mode
           ORDER BY date DESC LIMIT 200""",
        (user_id,),
    ).fetchall()

    # Wrong answers
    wrong_answers = db.execute(
        """SELECT character, pinyin, words, grade, mode, review_count, DATE(created_at) as date
           FROM wrong_answers WHERE user_id = %s
           ORDER BY created_at DESC""",
        (user_id,),
    ).fetchall()

    # Mastered words
    mastered = db.execute(
        """SELECT character, pinyin, words, grade, mode, DATE(mastered_at) as mastered_date
           FROM wrong_answer_events WHERE user_id = %s AND mastered = 1
           ORDER BY mastered_at DESC, id DESC""",
        (user_id,),
    ).fetchall()

    # Coin transactions — totals by source + per-day breakdown
    coin_totals = db.execute(
        """SELECT source,
                  COALESCE(SUM(CASE WHEN amount > 0 THEN amount ELSE 0 END), 0) as earned,
                  COALESCE(SUM(CASE WHEN amount < 0 THEN -amount ELSE 0 END), 0) as spent
           FROM coin_transactions WHERE user_id = %s GROUP BY source""",
        (user_id,),
    ).fetchall()
    coin_daily = db.execute(
        """SELECT DATE(created_at) as date, source,
                  COALESCE(SUM(amount), 0) as net,
                  COALESCE(SUM(CASE WHEN amount > 0 THEN amount ELSE 0 END), 0) as earned,
                  COALESCE(SUM(CASE WHEN amount < 0 THEN -amount ELSE 0 END), 0) as spent
           FROM coin_transactions WHERE user_id = %s
           GROUP BY DATE(created_at), source
           ORDER BY date DESC LIMIT 200""",
        (user_id,),
    ).fetchall()
    coin_recent = db.execute(
        """SELECT amount, source, mode, grade, details, created_at
           FROM coin_transactions WHERE user_id = %s
           ORDER BY created_at DESC LIMIT 50""",
        (user_id,),
    ).fetchall()
    exchange_recent = db.execute(
        """SELECT exchange_date, coins, minutes, created_at
           FROM exchange_records WHERE user_id = %s
           ORDER BY exchange_date DESC, created_at DESC, id DESC LIMIT 100""",
        (user_id,),
    ).fetchall()
    game_usage_recent = db.execute(
        """SELECT usage_date, minutes, purpose, created_at
           FROM game_usage_records WHERE user_id = %s
           ORDER BY usage_date DESC, created_at DESC, id DESC LIMIT 100""",
        (user_id,),
    ).fetchall()

    return jsonify({
        "user": dict(user),
        "scores": [dict(r) for r in scores],
        "wrong_answers": [dict(r) for r in wrong_answers],
        "mastered": [dict(r) for r in mastered],
        "coin_totals": [dict(r) for r in coin_totals],
        "coin_daily": [dict(r) for r in coin_daily],
        "coin_recent": [dict(r) for r in coin_recent],
        "exchange_recent": [dict(r) for r in exchange_recent],
        "game_usage_recent": [dict(r) for r in game_usage_recent],
    })


@app.route("/admin/user/<int:user_id>/wrong")
def admin_user_wrong_page(user_id):
    """Full-page view of a user's wrong answers (admin only)."""
    if not session.get("is_admin"):
        return redirect(url_for("index"))
    db = get_db()
    user = db.execute("SELECT username FROM users WHERE id = %s", (user_id,)).fetchone()
    if not user:
        return redirect(url_for("index"))
    return render_template("admin_wrong.html", user_id=user_id, username=user["username"])


@app.route("/api/admin/settings", methods=["GET", "POST"])
def admin_settings():
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    db = get_db()
    if request.method == "POST":
        data = request.get_json(force=True, silent=True)
        if not data:
            return jsonify({"error": "无效的请求数据"}), 400

        if "coin_rules" in data:
            rules = data["coin_rules"]
            # Validate structure
            for key in ("recognition", "writing"):
                if key not in rules or not isinstance(rules[key], list):
                    return jsonify({"error": f"缺少 {key} 规则"}), 400
                for m in rules[key]:
                    if not isinstance(m.get("streak"), int) or not isinstance(m.get("coins"), int):
                        return jsonify({"error": "规则格式错误: 需要 streak 和 coins 为整数"}), 400
            db.execute("INSERT INTO settings (key, value) VALUES ('coin_rules', %s) ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value",
                       (json.dumps(rules, ensure_ascii=False),))

        if "exchange_packages" in data:
            pkgs = data["exchange_packages"]
            if not isinstance(pkgs, list):
                return jsonify({"error": "兑换套餐格式错误"}), 400
            for p in pkgs:
                if not isinstance(p.get("price"), int) or not isinstance(p.get("minutes"), int):
                    return jsonify({"error": "套餐格式错误: 需要 price 和 minutes 为整数"}), 400
            db.execute("INSERT INTO settings (key, value) VALUES ('exchange_packages', %s) ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value",
                       (json.dumps(pkgs, ensure_ascii=False),))

        db.commit()
        return jsonify({"ok": True})

    return jsonify({
        "coin_rules": _get_coin_rules(db),
        "exchange_packages": _get_exchange_packages(db),
    })


# --- Shop & Coins routes ---

@app.route("/api/coins")
def coins_api():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    row = db.execute("SELECT coins, game_minutes, recognition_streak, writing_streak FROM users WHERE id = %s",
                     (session["user_id"],)).fetchone()
    return jsonify({
        "coins": row["coins"] if row else 0,
        "game_minutes": row["game_minutes"] if row else 0,
        "recognition_streak": row["recognition_streak"] if row else 0,
        "writing_streak": row["writing_streak"] if row else 0,
    })


def _coin_eligibility_info(db, user_id, mode, game_grade):
    """Return coin-streak eligibility for a game grade.

    Anti-cheating: prevent farming easy books. Free practice only counts
    toward the coin streak when it is no more than three books behind the
    user's current by-lesson homework book for that question type.
    """
    if not game_grade:
        return {"eligible": True, "message": ""}  # homework mode, no grade check needed

    is_writing = mode == "dictation_handwrite"

    plans = _active_homework_plans(db, user_id)
    plan = next((p for p in plans if (p["mode"] if "mode" in p.keys() else "by_lesson") == "by_lesson"), None)
    if not plan:
        return {"eligible": True, "message": ""}  # no by-lesson plan, allow freely

    if is_writing:
        hw_grade = plan["writing_grade"] or plan["grade"]
    else:
        hw_grade = plan["recognition_grade"] or plan["grade"]

    if hw_grade not in GRADE_ORDER or game_grade not in GRADE_ORDER:
        return {"eligible": True, "message": ""}

    hw_idx = GRADE_ORDER.index(hw_grade) if hw_grade in GRADE_ORDER else 0
    game_idx = GRADE_ORDER.index(game_grade) if game_grade in GRADE_ORDER else 0
    min_idx = max(0, hw_idx - COIN_STREAK_LOOKBACK_BOOKS)
    eligible = game_idx >= min_idx
    return {
        "eligible": eligible,
        "message": "" if eligible else COIN_INELIGIBLE_MESSAGE,
        "homework_grade": hw_grade,
        "eligible_from_grade": GRADE_ORDER[min_idx],
        "lookback_books": COIN_STREAK_LOOKBACK_BOOKS,
    }


def _check_coin_eligible(db, user_id, mode, game_grade):
    return _coin_eligibility_info(db, user_id, mode, game_grade)["eligible"]


@app.route("/api/coin-eligible")
def coin_eligible_check():
    """Check if a game mode + grade combination is eligible for coin awards."""
    if "user_id" not in session:
        return jsonify({"eligible": True})
    mode = request.args.get("mode", "")
    grade = request.args.get("grade", "")
    db = get_db()
    info = _coin_eligibility_info(db, session["user_id"], mode, grade)
    return jsonify(info)


@app.route("/api/streak", methods=["POST"])
def streak_update():
    """Update persistent streak on each answer. Awards coins at milestones."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    data = request.get_json(force=True, silent=True)
    if not data:
        return jsonify({"error": "无效的请求数据"}), 400

    correct = data.get("correct", False)
    mode = data.get("mode", "")
    game_grade = data.get("grade", "")  # grade of the game being played
    # source: 'game' | 'homework' — defaults to 'game' for legacy clients
    source = data.get("source", "game")
    if source not in ("game", "homework"):
        source = "game"
    is_writing = mode == "dictation_handwrite"
    STREAK_COLS = {
        "writing": ("writing_streak", "writing_coins_awarded"),
        "recognition": ("recognition_streak", "recognition_coins_awarded"),
    }
    streak_col, awarded_col = STREAK_COLS["writing" if is_writing else "recognition"]

    db = get_db()
    user = db.execute(
        psycopg.sql.SQL("SELECT {streak}, {awarded}, coins FROM users WHERE id = %s").format(
            streak=psycopg.sql.Identifier(streak_col),
            awarded=psycopg.sql.Identifier(awarded_col),
        ),
        (session["user_id"],),
    ).fetchone()
    if not user:
        return jsonify({"error": "用户不存在"}), 404

    # Check if this game grade participates in the coin streak.
    eligibility = _coin_eligibility_info(db, session["user_id"], mode, game_grade)
    coin_eligible = eligibility["eligible"]

    coins_earned = 0
    if not coin_eligible:
        # Out-of-range practice is ignored for the coin streak: it neither
        # increments nor resets the existing persistent streak.
        new_streak = user[streak_col]
    elif correct:
        new_streak = user[streak_col] + 1
        total_coins_at_streak = calc_streak_coins(new_streak, is_writing, db)
        coins_earned = total_coins_at_streak - user[awarded_col]
        if coins_earned > 0:
            db.execute(
                psycopg.sql.SQL("UPDATE users SET {streak} = %s, {awarded} = %s, coins = coins + %s WHERE id = %s").format(
                    streak=psycopg.sql.Identifier(streak_col),
                    awarded=psycopg.sql.Identifier(awarded_col),
                ),
                (new_streak, total_coins_at_streak, coins_earned, session["user_id"]),
            )
            db.execute(
                "INSERT INTO coin_transactions (user_id, amount, source, mode, grade, details) VALUES (%s, %s, %s, %s, %s, %s)",
                (session["user_id"], coins_earned, source, mode, game_grade,
                 f"连对 {new_streak} 次 · {'写字' if is_writing else '认字'}"),
            )
        else:
            db.execute(
                psycopg.sql.SQL("UPDATE users SET {streak} = %s WHERE id = %s").format(
                    streak=psycopg.sql.Identifier(streak_col),
                ),
                (new_streak, session["user_id"]),
            )
    else:
        new_streak = 0
        db.execute(
            psycopg.sql.SQL("UPDATE users SET {streak} = 0, {awarded} = 0 WHERE id = %s").format(
                streak=psycopg.sql.Identifier(streak_col),
                awarded=psycopg.sql.Identifier(awarded_col),
            ),
            (session["user_id"],),
        )

    db.commit()
    return jsonify({
        "streak": new_streak,
        "coins_earned": coins_earned,
        "coins": user["coins"] + coins_earned,
        "coin_eligible": coin_eligible,
        "coin_eligibility_message": eligibility["message"],
    })


@app.route("/api/shop")
def shop_api():
    db = get_db()
    packages = _get_exchange_packages(db)
    rules = _get_coin_rules(db)
    payload = {"items": packages, "coin_rules": rules}
    if "user_id" in session:
        exchange_recent, game_usage_recent = _game_time_records(db, session["user_id"], limit=50)
        payload["exchange_recent"] = exchange_recent
        payload["game_usage_recent"] = game_usage_recent
    return jsonify(payload)


@app.route("/api/shop/buy", methods=["POST"])
def shop_buy():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    data = request.get_json()
    package_id = data.get("item_id")

    db = get_db()
    packages = _get_exchange_packages(db)
    package = next((p for p in packages if p["id"] == package_id), None)
    if not package:
        return jsonify({"error": "套餐不存在"}), 404

    user = db.execute("SELECT coins, game_minutes FROM users WHERE id = %s", (session["user_id"],)).fetchone()
    if user["coins"] < package["price"]:
        return jsonify({"error": "金币不足"}), 400

    db.execute("UPDATE users SET coins = coins - %s, game_minutes = game_minutes + %s WHERE id = %s",
               (package["price"], package["minutes"], session["user_id"]))
    tx = db.execute(
        """INSERT INTO coin_transactions (user_id, amount, source, details)
           VALUES (%s, %s, 'shop', %s)
           RETURNING id, created_at""",
        (session["user_id"], -package["price"], f"兑换 {package['minutes']} 分钟游戏时间"),
    ).fetchone()
    tx_created_at = tx["created_at"]
    exchange_date = tx_created_at.date().isoformat() if hasattr(tx_created_at, "date") else str(tx_created_at)[:10]
    db.execute(
        """INSERT INTO exchange_records
           (user_id, exchange_date, coins, minutes, source_transaction_id, created_at)
           VALUES (%s, %s, %s, %s, %s, %s)
           ON CONFLICT (source_transaction_id) DO NOTHING""",
        (session["user_id"], exchange_date, package["price"], package["minutes"], tx["id"], tx_created_at),
    )
    db.commit()
    new_coins = user["coins"] - package["price"]
    new_minutes = user["game_minutes"] + package["minutes"]
    return jsonify({"ok": True, "coins": new_coins, "game_minutes": new_minutes})


# === Homework System ===

@app.route("/homework")
def homework_page():
    if "user_id" not in session:
        return redirect(url_for("index"))
    return render_template("homework.html", username=session["username"])


def _get_or_create_today_assignments(db, user_id):
    """Get or auto-create today's assignments for a user."""
    today = date.today().isoformat()

    plans = _active_homework_plans(db, user_id)
    if not plans:
        existing = db.execute(
            """SELECT * FROM daily_assignments
               WHERE user_id = %s AND date = %s
               ORDER BY CASE mode
                          WHEN 'by_lesson' THEN 0
                          WHEN 'book_review' THEN 1
                          ELSE 2
                        END,
                        type, id""",
            (user_id, today),
        ).fetchall()
        return [dict(r) for r in existing]

    # Carry any still-pending assignments from earlier days onto today so
    # the student keeps their saved_progress and isn't handed a fresh
    # assignment on top of unfinished work. Once they clear the carry-overs,
    # the usual auto-advance below picks up the next lesson.
    db.execute(
        "UPDATE daily_assignments SET date = %s "
        "WHERE user_id = %s AND date < %s AND status = 'pending'",
        (today, user_id, today),
    )
    db.commit()

    existing = db.execute(
        "SELECT * FROM daily_assignments WHERE user_id = %s AND date = %s",
        (user_id, today),
    ).fetchall()

    for plan in plans:
        plan_mode = plan["mode"] if "mode" in plan.keys() else "by_lesson"
        plan_existing = [
            r for r in existing
            if (r["mode"] if "mode" in r.keys() else "by_lesson") == plan_mode
        ]
        has_pending = any(r["status"] == "pending" for r in plan_existing)

        if plan_mode == "book_review":
            # Ensure the plan's current review day exists for each type. This
            # also recovers gracefully if a prior submit advanced the plan but
            # the newly-created assignment was lost before commit.
            changed = False
            for hw_type, day_col in [
                ("recognition", "recognition_lesson"),
                ("writing", "writing_lesson"),
            ]:
                type_rows = [r for r in plan_existing if r["type"] == hw_type]
                if any(r["status"] == "pending" for r in type_rows):
                    continue
                target_day = plan[day_col]
                split_key = "recognition" if hw_type == "recognition" else "writing"
                split = get_book_review_split(plan["grade"]).get(split_key, [])
                has_content = 1 <= target_day <= BOOK_REVIEW_DAYS and target_day - 1 < len(split) and bool(split[target_day - 1])
                if not has_content:
                    continue
                exists = any(r["grade"] == plan["grade"] and r["lesson_num"] == target_day for r in type_rows)
                if exists:
                    continue
                db.execute(
                    "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num, mode) VALUES (%s, %s, %s, %s, %s, 'book_review')",
                    (user_id, today, hw_type, plan["grade"], target_day),
                )
                changed = True
            if changed:
                db.commit()
            continue

        if not plan_existing:
            # First visit today: create initial assignments using cross-grade search
            rec_base_grade = plan["recognition_grade"] or plan["grade"]
            wrt_base_grade = plan["writing_grade"] or plan["grade"]
            rec_grade, rec_ln = find_next_lesson_across_grades(
                rec_base_grade, plan["recognition_lesson"], "识字")
            wrt_grade, wrt_ln = find_next_lesson_across_grades(
                wrt_base_grade, plan["writing_lesson"], "词语")
            if rec_grade and rec_ln:
                db.execute(
                    "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num, mode) VALUES (%s, %s, 'recognition', %s, %s, 'by_lesson')",
                    (user_id, today, rec_grade, rec_ln),
                )
            if wrt_grade and wrt_ln:
                db.execute(
                    "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num, mode) VALUES (%s, %s, 'writing', %s, %s, 'by_lesson')",
                    (user_id, today, wrt_grade, wrt_ln),
                )
            db.commit()
        elif not has_pending:
            # No pending work today — either (a) everything's done and we should
            # advance to the next lesson, or (b) one type was carried over and
            # completed but the other type has nothing for today yet. Both cases
            # call for creating a fresh assignment from the plan's current
            # lesson pointer for any type that either has no rows today at all
            # or only has completed rows.
            changed = False
            for hw_type, content_key in [("recognition", "识字"), ("writing", "词语")]:
                type_assignments = [dict(r) for r in plan_existing if r["type"] == hw_type]
                if any(a["status"] == "pending" for a in type_assignments):
                    continue  # should not happen — has_pending was False above
                plan_lesson = plan["recognition_lesson"] if hw_type == "recognition" else plan["writing_lesson"]
                base_grade = (plan["recognition_grade"] if hw_type == "recognition" else plan["writing_grade"]) or plan["grade"]
                next_grade, next_ln = find_next_lesson_across_grades(
                    base_grade, plan_lesson, content_key)
                if not next_grade:
                    continue
                dup = any(a["grade"] == next_grade and a["lesson_num"] == next_ln for a in type_assignments)
                if dup:
                    continue
                db.execute(
                    "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num, mode) VALUES (%s, %s, %s, %s, %s, 'by_lesson')",
                    (user_id, today, hw_type, next_grade, next_ln),
                )
                changed = True
            if changed:
                db.commit()

    rows = db.execute(
        """SELECT * FROM daily_assignments
           WHERE user_id = %s AND date = %s
           ORDER BY CASE mode
                      WHEN 'by_lesson' THEN 0
                      WHEN 'book_review' THEN 1
                      ELSE 2
                    END,
                    type, id""",
        (user_id, today),
    ).fetchall()
    return [dict(r) for r in rows]


@app.route("/api/homework/today")
def homework_today():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    assignments = _get_or_create_today_assignments(db, session["user_id"])
    plan_infos = [_homework_plan_info(p) for p in _active_homework_plans(db, session["user_id"])]
    plan_info = plan_infos[0] if plan_infos else None
    # Check if there are wrong answers from previous days needing review
    today = date.today().isoformat()
    review_items = db.execute(
        """SELECT DISTINCT ON (character, mode) character, pinyin, words, grade, mode, review_count
           FROM wrong_answers
           WHERE user_id = %s AND DATE(created_at) < %s
           ORDER BY character, mode, review_count ASC, created_at DESC""",
        (session["user_id"], today),
    ).fetchall()
    review_needed = [dict(r) for r in review_items]
    for item in review_needed:
        if item.get("mode") != "dictation_handwrite":
            item["words"] = _recognition_word_hint(
                item.get("character", ""), item.get("pinyin", ""),
                item.get("grade", ""), item.get("words", ""),
            )
    writing_chars = {r["character"] for r in review_needed if r["mode"] == "dictation_handwrite"}
    review_needed = [r for r in review_needed
                     if r["mode"] == "dictation_handwrite" or r["character"] not in writing_chars]

    return jsonify({
        "assignments": assignments,
        "plan": plan_info,
        "plans": plan_infos,
        "review_needed": review_needed,
    })


@app.route("/api/homework/review_submit", methods=["POST"])
def homework_review_submit():
    """Mark review items as reviewed after completing review quiz."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    data = request.get_json()
    items = data.get("items", [])
    db = get_db()
    delete_all = data.get("delete_all", False)
    today = date.today().isoformat()
    for item in items:
        character = item.get("character", "")
        mode = item.get("mode", "")
        if delete_all:
            # Voluntary review: delete all matching wrong answers
            db.execute(
                "DELETE FROM wrong_answers WHERE user_id = %s AND character = %s AND mode = %s",
                (session["user_id"], character, mode),
            )
        else:
            # Pre-homework review: only delete old wrong answers (before today)
            db.execute(
                "DELETE FROM wrong_answers WHERE user_id = %s AND character = %s AND mode = %s AND DATE(created_at) < %s",
                (session["user_id"], character, mode, today),
            )
    db.commit()
    return jsonify({"ok": True})


@app.route("/api/homework/start/<int:assignment_id>")
def homework_start(assignment_id):
    """Generate all questions for a homework assignment."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    assignment = db.execute(
        "SELECT * FROM daily_assignments WHERE id = %s AND user_id = %s",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    grade = assignment["grade"]
    lesson_num = assignment["lesson_num"]
    hw_type = assignment["type"]
    asn_mode = assignment["mode"] if "mode" in assignment.keys() else "by_lesson"

    # Collect raw entries for this assignment (both modes produce the same
    # {word, pinyin} shape, question-building then diverges by hw_type)
    if asn_mode == "book_review":
        split = get_book_review_split(grade)
        day = lesson_num
        if not (1 <= day <= BOOK_REVIEW_DAYS):
            return jsonify({"error": f"无效的复习天数: {day}"}), 400
        if hw_type == "recognition":
            entries = split["recognition"][day - 1]
        elif hw_type == "writing":
            entries = split["writing"][day - 1]
        else:
            entries = []
        if not entries:
            return jsonify({"error": "该天暂无数据"}), 400
    else:
        lessons = HOMEWORK_LESSONS.get(grade, {})
        lesson_data = lessons.get(lesson_num, {})
        if hw_type == "recognition":
            entries = lesson_data.get("认字", []) or lesson_data.get("识字", [])
            if not entries:
                return jsonify({"error": "该课暂无识字数据"}), 400
        elif hw_type == "writing":
            entries = [e for e in lesson_data.get("词语", []) if len(e.get("word", "")) >= 2]
            if not entries:
                return jsonify({"error": "该课暂无词语数据"}), 400
        else:
            entries = []

    questions = []
    if hw_type == "recognition":
        all_chars = CHARACTERS.get(grade, [])
        for entry in entries:
            word_hint_list = []
            for c in all_chars:
                if c["char"] == entry["word"]:
                    word_hint_list = c.get("words", [])
                    break
            # For single multi-pronunciation characters, add context word
            context_word = ""
            char_text = entry["word"]
            if len(char_text) == 1 and char_text in MULTI_PINYIN:
                # context lookup uses lesson_num only in by_lesson mode; in
                # book_review the lesson_num is a day index and the lookup
                # would come up empty — passing it is harmless.
                context_word = _find_context_word(
                    char_text, entry["pinyin"], grade, lesson_num)
            # Recognition homework uses pinyin typing mode (给汉字注音)
            q = {
                "mode": "pinyin_typing",
                "question": entry["word"],
                "answer": entry["pinyin"],
                "word_hint": _recognition_word_hint(entry["word"], entry["pinyin"], grade, "、".join(word_hint_list)),
                "display_char": entry["word"],
                "display_pinyin": entry["pinyin"],
            }
            if context_word:
                q["context_word"] = context_word
            questions.append(q)
        random.shuffle(questions)
    elif hw_type == "writing":
        for entry in entries:
            if len(entry["word"]) < 2:
                continue
            q = {
                "mode": "dictation_handwrite",
                "question": entry["pinyin"],
                "answer": entry["word"],
                "display_char": entry["word"], "display_pinyin": entry["pinyin"],
            }
            if _pinyin_has_other_word(entry["pinyin"], entry["word"]):
                hint = HOMOPHONE_HINTS.get(entry["word"])
                if hint:
                    q["homophone_hint"] = hint
            questions.append(q)
        random.shuffle(questions)

    # Check for saved progress
    saved = assignment.get("saved_progress", "") or ""
    saved_data = None
    if saved:
        try:
            saved_data = json.loads(saved)
        except (json.JSONDecodeError, TypeError):
            saved_data = None

    resp = {
        "assignment_id": assignment_id,
        "type": hw_type,
        "grade": grade,
        "lesson_num": lesson_num,
        "questions": questions,
        "total": len(questions),
    }
    if saved_data:
        resp["saved_progress"] = saved_data
    return jsonify(resp)


@app.route("/api/homework/preview/<int:assignment_id>")
def homework_preview(assignment_id):
    """Generate preview (预习) questions for a homework assignment.
    Supports modes: char_to_pinyin, pinyin_to_char, listen_to_char."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    assignment = db.execute(
        "SELECT * FROM daily_assignments WHERE id = %s AND user_id = %s",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    grade = assignment["grade"]
    lesson_num = assignment["lesson_num"]
    asn_mode = assignment["mode"] if "mode" in assignment.keys() else "by_lesson"
    hw_type = assignment["type"]
    mode = request.args.get("mode", "char_to_pinyin")
    if mode not in ("char_to_pinyin", "pinyin_to_char", "listen_to_char"):
        mode = "char_to_pinyin"

    # 分册复习: preview must use the exact same pool as the day's homework.
    # lesson_num here is a day index (1..7) into the book-review split, not
    # a lesson number, so looking it up in HOMEWORK_LESSONS would return
    # the wrong content (or nothing).
    if asn_mode == "book_review":
        split = get_book_review_split(grade)
        day = lesson_num
        if not (1 <= day <= BOOK_REVIEW_DAYS):
            return jsonify({"error": f"无效的复习天数: {day}"}), 400
        entries = split.get(hw_type, [[]])[day - 1] if hw_type in ("recognition", "writing") else []
    else:
        lessons = HOMEWORK_LESSONS.get(grade, {})
        lesson_data = lessons.get(lesson_num, {})
        entries = lesson_data.get("认字", []) or lesson_data.get("识字", [])

    if not entries:
        return jsonify({"error": "该课暂无数据"}), 400

    all_chars = CHARACTERS.get(grade, [])
    grade_words = WORDS.get(grade, [])
    # Pre-build a length -> candidate word list so multi-char entries get
    # matching-字数 distractors without O(n) rescans per question.
    words_by_len: dict[int, list[dict]] = {}
    for w in grade_words:
        words_by_len.setdefault(len(w["word"]), []).append(
            {"char": w["word"], "pinyin": w["pinyin"], "words": []}
        )

    questions = []
    for entry in entries:
        word_text = entry["word"]
        correct = {"char": word_text, "pinyin": entry["pinyin"], "words": []}
        if len(word_text) == 1:
            # Single char: use CHARACTERS pool for hints + distractors
            correct["words"] = _char_word_examples(word_text, entry["pinyin"], grade)
            others = [c for c in all_chars if c["char"] != word_text]
        else:
            # Multi-char 词语: pool = same-length 词语 from this grade, falling
            # back to all grades if fewer than 4 candidates exist.
            others = [c for c in words_by_len.get(len(word_text), []) if c["char"] != word_text]
            if len(others) < 4:
                for g, ws in WORDS.items():
                    if g == grade:
                        continue
                    for w in ws:
                        if len(w["word"]) == len(word_text) and w["word"] != word_text:
                            others.append({"char": w["word"], "pinyin": w["pinyin"], "words": []})

        if mode == "char_to_pinyin":
            distractors = _pick_distractors(correct, others, key="pinyin")
            options = [correct["pinyin"]] + [d["pinyin"] for d in distractors]
            random.shuffle(options)
            q = {
                "mode": mode, "question": correct["char"],
                "options": options, "correct_index": options.index(correct["pinyin"]),
                "answer": correct["pinyin"],
                "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
                "display_char": correct["char"], "display_pinyin": correct["pinyin"],
            }
            if correct["char"] in MULTI_PINYIN:
                cw = _find_context_word(correct["char"], correct["pinyin"], grade, lesson_num)
                if not cw and correct.get("words"):
                    cw = correct["words"][0]
                if cw:
                    q["context_word"] = cw
            questions.append(q)
        elif mode == "pinyin_to_char":
            distractors = _pick_distractors(correct, others, key="char")
            options = [correct["char"]] + [d["char"] for d in distractors]
            random.shuffle(options)
            questions.append({
                "mode": mode, "question": correct["pinyin"],
                "options": options, "correct_index": options.index(correct["char"]),
                "answer": correct["char"],
                "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
                "display_char": correct["char"], "display_pinyin": correct["pinyin"],
            })
        elif mode == "listen_to_char":
            distractors = _pick_distractors(correct, others, key="char",
                                            exclude_homophones=True)
            options = [correct["char"]] + [d["char"] for d in distractors]
            random.shuffle(options)
            questions.append({
                "mode": mode, "question": correct["char"],
                "question_pinyin": correct["pinyin"],
                "options": options, "correct_index": options.index(correct["char"]),
                "answer": correct["char"],
                "word_hint": _recognition_word_hint(correct["char"], correct["pinyin"], grade, "、".join(correct["words"])),
                "display_char": correct["char"], "display_pinyin": correct["pinyin"],
            })

    random.shuffle(questions)
    return jsonify({
        "assignment_id": assignment_id,
        "grade": grade,
        "lesson_num": lesson_num,
        "questions": questions,
        "total": len(questions),
    })


@app.route("/api/homework/submit", methods=["POST"])
def homework_submit():
    """Submit completed homework assignment results."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    data = request.get_json()
    assignment_id = data.get("assignment_id")
    total_questions = data.get("total_questions", 0)
    correct_answers = data.get("correct_answers", 0)
    try:
        time_spent = int(data.get("time_spent", 0) or 0)
    except (TypeError, ValueError):
        time_spent = 0
    time_spent = max(0, min(time_spent, 12 * 60 * 60))
    wrong_item_list = data.get("wrong_items", [])
    if not isinstance(wrong_item_list, list):
        wrong_item_list = []
    wrong_items = json.dumps(wrong_item_list, ensure_ascii=False)

    db = get_db()
    assignment = db.execute(
        "SELECT * FROM daily_assignments WHERE id = %s AND user_id = %s",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    # Update assignment
    db.execute(
        """UPDATE daily_assignments
           SET status = 'completed', total_questions = %s, correct_answers = %s,
               time_spent = %s, wrong_items = %s, saved_progress = '',
               completed_at = CURRENT_TIMESTAMP
           WHERE id = %s""",
        (total_questions, correct_answers, time_spent, wrong_items, assignment_id),
    )

    asn_mode = assignment["mode"] if "mode" in assignment.keys() else "by_lesson"
    # Advance the plan pointer if this assignment was completed for the first
    # time. Repeated assignments keep the plan where it is.
    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = %s AND active = 1 AND mode = %s ORDER BY id DESC LIMIT 1",
        (session["user_id"], asn_mode),
    ).fetchone()
    first_completion = bool(plan and assignment["status"] == "pending")
    if first_completion:
        if asn_mode == "book_review":
            next_day = find_next_book_review_day(
                assignment["grade"], assignment["lesson_num"], assignment["type"]
            )
            if next_day:
                if assignment["type"] == "recognition":
                    db.execute("UPDATE homework_plans SET recognition_lesson = %s WHERE id = %s",
                               (next_day, plan["id"]))
                else:
                    db.execute("UPDATE homework_plans SET writing_lesson = %s WHERE id = %s",
                               (next_day, plan["id"]))
        else:
            content_key = "识字" if assignment["type"] == "recognition" else "词语"
            if assignment["type"] == "recognition":
                base_grade = plan["recognition_grade"] or plan["grade"]
                current_lesson = plan["recognition_lesson"]
            else:
                base_grade = plan["writing_grade"] or plan["grade"]
                current_lesson = plan["writing_lesson"]

            next_grade, next_ln = find_next_lesson_across_grades(base_grade, current_lesson + 1, content_key)
            if next_grade and next_ln:
                if assignment["type"] == "recognition":
                    db.execute("UPDATE homework_plans SET recognition_lesson = %s, recognition_grade = %s WHERE id = %s",
                               (next_ln, next_grade, plan["id"]))
                else:
                    db.execute("UPDATE homework_plans SET writing_lesson = %s, writing_grade = %s WHERE id = %s",
                               (next_ln, next_grade, plan["id"]))

    # Also record wrong answers in the main wrong_answers table
    source_label = _source_label(
        "homework",
        grade=assignment["grade"],
        assignment_type=assignment["type"],
        lesson_num=assignment["lesson_num"],
        assignment_mode=asn_mode,
    )
    for idx, item in enumerate(wrong_item_list):
        item_mode = item.get("mode", "")
        item_words = item.get("words", "")
        if item_mode != "dictation_handwrite":
            item_words = _recognition_word_hint(
                item.get("character", ""), item.get("pinyin", ""),
                assignment["grade"], item_words,
            )
        db.execute(
            "INSERT INTO wrong_answers (user_id, character, pinyin, words, grade, mode) VALUES (%s, %s, %s, %s, %s, %s)",
            (session["user_id"], item.get("character", ""), item.get("pinyin", ""),
             item_words, assignment["grade"], item_mode),
        )
        payload = _wrong_item_payload(item, fallback_grade=assignment["grade"])
        event_key = f"homework:{assignment_id}:{idx}:{payload['character']}:{payload['mode']}"
        _insert_wrong_event(
            db,
            session["user_id"],
            item,
            source="homework",
            source_id=assignment_id,
            source_date=assignment["date"],
            source_label=source_label,
            event_key=event_key,
            fallback_grade=assignment["grade"],
        )

    # Coins are now awarded in real-time via /api/streak during the quiz
    coins_earned = 0

    # Auto-create the next assignment if this was first completion.
    next_assignment = None
    if first_completion:
        today = date.today().isoformat()
        # Re-read the updated plan to get the advanced grade/lesson
        updated_plan = db.execute(
            "SELECT * FROM homework_plans WHERE id = %s", (plan["id"],)
        ).fetchone()
        if asn_mode == "book_review":
            next_grade = updated_plan["grade"]
            next_lesson = updated_plan["recognition_lesson"] if assignment["type"] == "recognition" else updated_plan["writing_lesson"]
            split_key = "recognition" if assignment["type"] == "recognition" else "writing"
            split = get_book_review_split(next_grade).get(split_key, [])
            has_content = 1 <= next_lesson <= BOOK_REVIEW_DAYS and next_lesson - 1 < len(split) and bool(split[next_lesson - 1])
        else:
            if assignment["type"] == "recognition":
                next_grade = updated_plan["recognition_grade"] or updated_plan["grade"]
                next_lesson = updated_plan["recognition_lesson"]
            else:
                next_grade = updated_plan["writing_grade"] or updated_plan["grade"]
                next_lesson = updated_plan["writing_lesson"]

            # Check the next lesson actually has content
            next_lessons = HOMEWORK_LESSONS.get(next_grade, {})
            content_key = "识字" if assignment["type"] == "recognition" else "词语"
            has_content = bool(next_lessons.get(next_lesson, {}).get(content_key))

        if has_content and not (next_grade == assignment["grade"] and next_lesson == assignment["lesson_num"]):
            # Check no duplicate for same type+grade+lesson today
            dup = db.execute(
                "SELECT id FROM daily_assignments WHERE user_id = %s AND date = %s AND type = %s AND grade = %s AND lesson_num = %s AND mode = %s",
                (session["user_id"], today, assignment["type"], next_grade, next_lesson, asn_mode),
            ).fetchone()
            if not dup:
                cur = db.execute(
                    "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num, mode) VALUES (%s, %s, %s, %s, %s, %s) RETURNING id",
                    (session["user_id"], today, assignment["type"], next_grade, next_lesson, asn_mode),
                )
                next_assignment = {
                    "id": cur.fetchone()["id"],
                    "type": assignment["type"],
                    "grade": next_grade,
                    "lesson_num": next_lesson,
                    "mode": asn_mode,
                }

    db.commit()

    # Check if both assignments for today are completed
    today = date.today().isoformat()
    pending = db.execute(
        "SELECT COUNT(*) as cnt FROM daily_assignments WHERE user_id = %s AND date = %s AND status != 'completed'",
        (session["user_id"], today),
    ).fetchone()

    all_done = pending["cnt"] == 0

    return jsonify({"ok": True, "coins_earned": coins_earned, "all_done": all_done, "next_assignment": next_assignment})


@app.route("/api/homework/save_progress", methods=["POST"])
def homework_save_progress():
    """Save partial homework progress so user can resume later."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    data = request.get_json()
    assignment_id = data.get("assignment_id")
    progress = data.get("progress")  # JSON string with currentIndex, correctCount, wrongItems, questions, timeElapsed
    if not assignment_id or progress is None:
        return jsonify({"error": "参数错误"}), 400
    db = get_db()
    assignment = db.execute(
        "SELECT * FROM daily_assignments WHERE id = %s AND user_id = %s",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404
    db.execute(
        "UPDATE daily_assignments SET saved_progress = %s WHERE id = %s",
        (json.dumps(progress, ensure_ascii=False), assignment_id),
    )
    db.commit()
    return jsonify({"ok": True})


@app.route("/api/homework/progress")
def homework_progress():
    """Get homework progress for all grades."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    db = get_db()
    plans = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = %s ORDER BY id",
        (session["user_id"],),
    ).fetchall()

    progress = []
    for p in plans:
        rec_grade = p["recognition_grade"] or p["grade"]
        wrt_grade = p["writing_grade"] or p["grade"]
        p_mode = p["mode"] if "mode" in p.keys() else "by_lesson"
        # Per UX: only show by_lesson plans on the progress dashboard.
        # Book-review progress is tracked elsewhere.
        if p_mode != "by_lesson":
            continue
        rec_total = len(HOMEWORK_LESSONS.get(rec_grade, {}))
        wrt_total = len(HOMEWORK_LESSONS.get(wrt_grade, {}))
        rec_pct = round((p["recognition_lesson"] - 1) / rec_total * 100) if rec_total > 0 else 0
        wrt_pct = round((p["writing_lesson"] - 1) / wrt_total * 100) if wrt_total > 0 else 0
        overall_pct = round((rec_pct + wrt_pct) / 2)
        progress.append({
            "grade": p["grade"],
            "grade_short": grade_short_name(p["grade"]),
            "recognition_grade": rec_grade,
            "writing_grade": wrt_grade,
            "recognition_lesson": p["recognition_lesson"],
            "writing_lesson": p["writing_lesson"],
            "rec_total_lessons": rec_total,
            "wrt_total_lessons": wrt_total,
            "total_lessons": max(rec_total, wrt_total),
            "recognition_pct": rec_pct,
            "writing_pct": wrt_pct,
            "overall_pct": overall_pct,
            "active": p["active"],
            "mode": p_mode,
        })

    # Also include recent history (last 7 days)
    week_ago = (date.today() - timedelta(days=7)).isoformat()
    history = db.execute(
        """SELECT date, type, grade, lesson_num, mode, status, total_questions, correct_answers, time_spent
           FROM daily_assignments WHERE user_id = %s AND date >= %s
           ORDER BY date DESC, type""",
        (session["user_id"], week_ago),
    ).fetchall()

    return jsonify({"progress": progress, "history": [dict(r) for r in history]})


# --- Admin Homework Routes ---

@app.route("/api/admin/homework/plan", methods=["POST"])
def admin_homework_plan():
    """Create or update a homework plan for a user.

    mode = 'by_lesson'   — recognition_lesson/writing_lesson are lesson numbers
    mode = 'book_review' — recognition_lesson/writing_lesson are day numbers 1..7
                           (content comes from get_book_review_split)
    """
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    data = request.get_json(force=True, silent=True)
    if not data:
        return jsonify({"error": "无效的请求数据"}), 400
    user_id = data.get("user_id")
    grade = data.get("grade", "")
    rec_lesson = int(data.get("recognition_lesson", 1) or 1)
    wrt_lesson = int(data.get("writing_lesson", 1) or 1)
    mode = data.get("mode", "by_lesson")

    if grade not in HOMEWORK_LESSONS:
        return jsonify({"error": f"无效年级: {grade}"}), 400
    if mode not in ("by_lesson", "book_review"):
        return jsonify({"error": f"无效模式: {mode}"}), 400
    if mode == "book_review":
        if not (1 <= rec_lesson <= BOOK_REVIEW_DAYS) or not (1 <= wrt_lesson <= BOOK_REVIEW_DAYS):
            return jsonify({"error": f"分册复习的天数需在 1-{BOOK_REVIEW_DAYS} 之间"}), 400
    else:
        total_lessons = len(HOMEWORK_LESSONS.get(grade, {}))
        if not (1 <= rec_lesson <= total_lessons) or not (1 <= wrt_lesson <= total_lessons):
            return jsonify({"error": f"{grade} 共 {total_lessons} 课，课号需在 1-{total_lessons} 之间"}), 400

    db = get_db()
    # Keep one active plan per mode, allowing by-lesson homework and book
    # review homework to be assigned at the same time.
    db.execute("UPDATE homework_plans SET active = 0 WHERE user_id = %s AND mode = %s", (user_id, mode))
    # Delete today's pending assignments so new plan takes effect immediately
    today = date.today().isoformat()
    db.execute(
        "DELETE FROM daily_assignments WHERE user_id = %s AND date = %s AND status = 'pending' AND mode = %s",
        (user_id, today, mode),
    )
    # Create new plan with separate grade tracking for each type
    db.execute(
        "INSERT INTO homework_plans (user_id, grade, recognition_lesson, writing_lesson, recognition_grade, writing_grade, mode) VALUES (%s, %s, %s, %s, %s, %s, %s)",
        (user_id, grade, rec_lesson, wrt_lesson, grade, grade, mode),
    )
    db.commit()
    return jsonify({"ok": True})


@app.route("/api/admin/homework/repeat", methods=["POST"])
def admin_homework_repeat():
    """Repeat an assignment - create a copy for tomorrow with same lesson."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    data = request.get_json(force=True, silent=True)
    if not data:
        return jsonify({"error": "无效的请求数据"}), 400
    assignment_id = data.get("assignment_id")

    db = get_db()
    assignment = db.execute("SELECT * FROM daily_assignments WHERE id = %s", (assignment_id,)).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    # Create repeat for tomorrow
    tomorrow = (date.today() + timedelta(days=1)).isoformat()
    asn_mode = assignment["mode"] if "mode" in assignment.keys() else "by_lesson"
    # Remove any existing assignment of same type and mode for tomorrow
    db.execute(
        "DELETE FROM daily_assignments WHERE user_id = %s AND date = %s AND type = %s AND mode = %s",
        (assignment["user_id"], tomorrow, assignment["type"], asn_mode),
    )
    db.execute(
        "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num, mode) VALUES (%s, %s, %s, %s, %s, %s)",
        (assignment["user_id"], tomorrow, assignment["type"], assignment["grade"], assignment["lesson_num"], asn_mode),
    )
    # Roll back the lesson advancement (by_lesson only — book_review never
    # auto-advanced, so nothing to roll back).
    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = %s AND active = 1 AND mode = %s ORDER BY id DESC LIMIT 1",
        (assignment["user_id"], asn_mode),
    ).fetchone()
    if plan and asn_mode != "book_review":
        if assignment["type"] == "recognition":
            db.execute(
                "UPDATE homework_plans SET recognition_lesson = %s, recognition_grade = %s WHERE id = %s",
                (assignment["lesson_num"], assignment["grade"], plan["id"]),
            )
        else:
            db.execute(
                "UPDATE homework_plans SET writing_lesson = %s, writing_grade = %s WHERE id = %s",
                (assignment["lesson_num"], assignment["grade"], plan["id"]),
            )
    db.commit()
    return jsonify({"ok": True})


@app.route("/api/admin/homework/overview")
def admin_homework_overview():
    """Get all users' homework status for admin."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    db = get_db()
    today = date.today().isoformat()

    users = db.execute("SELECT id, username FROM users").fetchall()
    result = []
    for u in users:
        plans = _active_homework_plans(db, u["id"])
        if not plans:
            continue

        assignments = db.execute(
            """SELECT * FROM daily_assignments
               WHERE user_id = %s AND date = %s
               ORDER BY CASE mode
                          WHEN 'by_lesson' THEN 0
                          WHEN 'book_review' THEN 1
                          ELSE 2
                        END,
                        type, id""",
            (u["id"], today),
        ).fetchall()

        for plan in plans:
            plan_info = _homework_plan_info(plan)
            p_mode = plan_info["mode"]
            plan_assignments = [
                dict(a) for a in assignments
                if (a["mode"] if "mode" in a.keys() else "by_lesson") == p_mode
            ]
            result.append({
                "user_id": u["id"],
                "username": u["username"],
                **plan_info,
                "today_assignments": plan_assignments,
            })

    # Get available grades info
    grades_info = []
    for g in GRADE_ORDER:
        if g in HOMEWORK_LESSONS:
            grades_info.append({"grade": g, "short": grade_short_name(g), "total_lessons": len(HOMEWORK_LESSONS[g])})

    return jsonify({"users": result, "grades": grades_info})


@app.route("/api/admin/user/<int:user_id>/daily_log")
def admin_user_daily_log(user_id):
    """Get daily activity log for a user (homework + game sessions)."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    db = get_db()
    days = int(request.args.get("days", 14))
    start_date = (date.today() - timedelta(days=days)).isoformat()

    # Homework records
    hw_rows = db.execute(
        """SELECT date, type, grade, lesson_num, status, total_questions, correct_answers, time_spent
           FROM daily_assignments WHERE user_id = %s AND date >= %s
           ORDER BY date DESC, type""",
        (user_id, start_date),
    ).fetchall()

    # Game session records (scores)
    game_rows = db.execute(
        """SELECT DATE(created_at) as date, grade, mode, total_questions, correct_answers, score
           FROM scores WHERE user_id = %s AND DATE(created_at) >= %s
           ORDER BY created_at DESC""",
        (user_id, start_date),
    ).fetchall()

    # Coin transactions per day+source (for "每日记录" coin column)
    coin_rows = db.execute(
        """SELECT DATE(created_at) as date, source,
                  COALESCE(SUM(CASE WHEN amount > 0 THEN amount ELSE 0 END), 0) as earned,
                  COALESCE(SUM(CASE WHEN amount < 0 THEN -amount ELSE 0 END), 0) as spent
           FROM coin_transactions
           WHERE user_id = %s AND DATE(created_at) >= %s
           GROUP BY DATE(created_at), source""",
        (user_id, start_date),
    ).fetchall()
    exchange_rows = db.execute(
        """SELECT exchange_date as date, coins, minutes, created_at
           FROM exchange_records
           WHERE user_id = %s AND exchange_date >= %s
           ORDER BY exchange_date DESC, created_at DESC, id DESC""",
        (user_id, start_date),
    ).fetchall()
    usage_rows = db.execute(
        """SELECT usage_date as date, minutes, purpose, created_at
           FROM game_usage_records
           WHERE user_id = %s AND usage_date >= %s
           ORDER BY usage_date DESC, created_at DESC, id DESC""",
        (user_id, start_date),
    ).fetchall()

    # Group by date (normalize keys to strings for consistent merging)
    daily_log = {}
    def _ensure(d):
        if d not in daily_log:
            daily_log[d] = {
                "date": d, "homework": [], "games": [], "exchanges": [], "game_usage": [],
                "coins": {"game": 0, "homework": 0, "shop": 0, "admin": 0, "net": 0},
            }
        return daily_log[d]

    for row in hw_rows:
        _ensure(str(row["date"]))["homework"].append(dict(row))
    for row in game_rows:
        _ensure(str(row["date"]))["games"].append(dict(row))
    for row in exchange_rows:
        _ensure(str(row["date"]))["exchanges"].append(dict(row))
    for row in usage_rows:
        _ensure(str(row["date"]))["game_usage"].append(dict(row))
    for row in coin_rows:
        d = str(row["date"])
        bucket = _ensure(d)["coins"]
        src = row["source"]
        if src == "shop":
            bucket["shop"] += row["spent"]
            bucket["net"] -= row["spent"]
        elif src in ("game", "homework", "admin"):
            bucket[src] += row["earned"]
            bucket["net"] += row["earned"]

    # Sort by date descending
    result = sorted(daily_log.values(), key=lambda x: x["date"], reverse=True)
    return jsonify({"daily_log": result})


@app.route("/api/admin/user/<int:user_id>/game_usage_records", methods=["POST"])
def admin_add_game_usage_record(user_id):
    """Add a manual game usage record for a user."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    data = request.get_json(silent=True) or {}
    usage_date = str(data.get("date") or "").strip()
    purpose = str(data.get("purpose") or "").strip()
    try:
        minutes = int(data.get("minutes") or 0)
    except (TypeError, ValueError):
        minutes = 0

    if not usage_date:
        usage_date = date.today().isoformat()
    try:
        datetime.strptime(usage_date, "%Y-%m-%d")
    except ValueError:
        return jsonify({"error": "日期格式需要是 YYYY-MM-DD"}), 400
    if minutes <= 0:
        return jsonify({"error": "请输入游戏使用分钟数"}), 400
    if not purpose:
        return jsonify({"error": "请选择或输入目的"}), 400

    db = get_db()
    user = db.execute("SELECT id FROM users WHERE id = %s", (user_id,)).fetchone()
    if not user:
        return jsonify({"error": "用户不存在"}), 404
    db.execute(
        """INSERT INTO game_usage_records (user_id, usage_date, minutes, purpose)
           VALUES (%s, %s, %s, %s)""",
        (user_id, usage_date, minutes, purpose),
    )
    db.commit()
    return jsonify({"ok": True})


@app.route("/api/tts")
def tts():
    text = request.args.get("text", "").strip()
    if not text:
        return "Missing text", 400

    elongate = request.args.get("elongate", "false") == "true"
    spoken_text = "，".join([text + "～～～～"] * 3) if elongate else text

    async def generate_audio():
        rate = "-70%" if elongate else "-30%"
        communicate = edge_tts.Communicate(spoken_text, voice="zh-CN-YunyangNeural", rate=rate, volume="+50%")
        buf = io.BytesIO()
        async for chunk in communicate.stream():
            if chunk["type"] == "audio":
                buf.write(chunk["data"])
        return buf.getvalue()

    audio_data = asyncio.run(generate_audio())
    return Response(audio_data, mimetype="audio/mpeg")


@app.route("/api/check_pronunciation", methods=["POST"])
def check_pronunciation():
    """Check if recognized text matches target pronunciation.

    Compares by pinyin (tone-insensitive) so homophones are accepted.
    E.g., recognizing 顶 for target 鼎 (both dǐng) → correct.
    Uses pypinyin for comprehensive character coverage beyond curriculum.
    """
    import pypinyin

    data = request.get_json(force=True, silent=True)
    if not data:
        return jsonify({"error": "无效的请求数据"}), 400

    recognized_texts = data.get("recognized", [])  # list of alternatives
    target_pinyin = data.get("target_pinyin", "")   # e.g. "dǐng"

    target_base = _strip_tone(target_pinyin.lower())

    for text in recognized_texts:
        for ch in text:
            # Get all possible pinyin readings for this character
            readings = pypinyin.pinyin(ch, style=pypinyin.Style.TONE, heteronym=True)
            if readings and readings[0]:
                for py in readings[0]:
                    if _strip_tone(py.lower()) == target_base:
                        return jsonify({"correct": True, "matched": ch, "pinyin": py})

    return jsonify({"correct": False})


if __name__ == "__main__":
    app.run(debug=False, host="127.0.0.1", port=5001)
