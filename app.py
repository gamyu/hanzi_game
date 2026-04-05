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
import hashlib
import io
import json
import os
import random
import sqlite3
import urllib.request
from datetime import date, datetime, timedelta

import edge_tts
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


def _find_context_word(char: str, pinyin: str, grade: str, lesson_num: int) -> str:
    """Find a context word for a multi-pronunciation character.
    Searches: 1) lesson vocabulary, 2) lesson text entries, 3) grade WORDS."""
    lesson_data = HOMEWORK_LESSONS.get(grade, {}).get(lesson_num, {})

    # 1. Search lesson 词语 entries
    for entry in lesson_data.get("词语", []):
        word = entry["word"]
        syllables = entry["pinyin"].split()
        if len(word) == len(syllables):
            for i, (ch, py) in enumerate(zip(word, syllables)):
                if ch == char and py == pinyin:
                    return word

    # 2. Search lesson 识字 entries (multi-char words)
    for entry in lesson_data.get("识字", []):
        if len(entry["word"]) >= 2:
            word = entry["word"]
            syllables = entry["pinyin"].split()
            if len(word) == len(syllables):
                for ch, py in zip(word, syllables):
                    if ch == char and py == pinyin:
                        return word

    # 3. Search CHARACTERS words hints for this grade
    for c in CHARACTERS.get(grade, []):
        if c["char"] == char and c["pinyin"] == pinyin:
            if c.get("words"):
                return c["words"][0]

    # 4. Search all WORDS in this grade
    for w in WORDS.get(grade, []):
        word = w["word"]
        syllables = w["pinyin"].split()
        if len(word) == len(syllables):
            for ch, py in zip(word, syllables):
                if ch == char and py == pinyin:
                    return word

    return ""


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
    return grade[0] + grade[-1]


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
app.secret_key = os.environ.get("SECRET_KEY", os.urandom(32))

ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "admin123")

DATABASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hanzi.db")


def get_db():
    if "db" not in g:
        g.db = sqlite3.connect(DATABASE)
        g.db.row_factory = sqlite3.Row
    return g.db


@app.teardown_appcontext
def close_db(exc):
    db = g.pop("db", None)
    if db is not None:
        db.close()


def init_db():
    db = sqlite3.connect(DATABASE)
    db.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS scores (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
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
            id INTEGER PRIMARY KEY AUTOINCREMENT,
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
        CREATE TABLE IF NOT EXISTS mastered_words (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
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
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            description TEXT DEFAULT '',
            price INTEGER NOT NULL,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS purchases (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
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
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            grade TEXT NOT NULL,
            recognition_lesson INTEGER NOT NULL DEFAULT 1,
            writing_lesson INTEGER NOT NULL DEFAULT 1,
            recognition_grade TEXT NOT NULL DEFAULT '',
            writing_grade TEXT NOT NULL DEFAULT '',
            active INTEGER NOT NULL DEFAULT 1,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    db.execute("""
        CREATE TABLE IF NOT EXISTS daily_assignments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            date TEXT NOT NULL,
            type TEXT NOT NULL,
            grade TEXT NOT NULL,
            lesson_num INTEGER NOT NULL,
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
    cols = [row[1] for row in db.execute("PRAGMA table_info(scores)").fetchall()]
    if "total_questions" not in cols:
        db.execute("ALTER TABLE scores ADD COLUMN total_questions INTEGER NOT NULL DEFAULT 0")
    if "correct_answers" not in cols:
        db.execute("ALTER TABLE scores ADD COLUMN correct_answers INTEGER NOT NULL DEFAULT 0")
    wa_cols = [row[1] for row in db.execute("PRAGMA table_info(wrong_answers)").fetchall()]
    if "review_count" not in wa_cols:
        db.execute("ALTER TABLE wrong_answers ADD COLUMN review_count INTEGER NOT NULL DEFAULT 0")
    user_cols = [row[1] for row in db.execute("PRAGMA table_info(users)").fetchall()]
    if "coins" not in user_cols:
        db.execute("ALTER TABLE users ADD COLUMN coins INTEGER NOT NULL DEFAULT 0")
    if "game_minutes" not in user_cols:
        db.execute("ALTER TABLE users ADD COLUMN game_minutes INTEGER NOT NULL DEFAULT 0")
    if "recognition_streak" not in user_cols:
        db.execute("ALTER TABLE users ADD COLUMN recognition_streak INTEGER NOT NULL DEFAULT 0")
    if "writing_streak" not in user_cols:
        db.execute("ALTER TABLE users ADD COLUMN writing_streak INTEGER NOT NULL DEFAULT 0")
    if "recognition_coins_awarded" not in user_cols:
        db.execute("ALTER TABLE users ADD COLUMN recognition_coins_awarded INTEGER NOT NULL DEFAULT 0")
    if "writing_coins_awarded" not in user_cols:
        db.execute("ALTER TABLE users ADD COLUMN writing_coins_awarded INTEGER NOT NULL DEFAULT 0")
    # Migrate homework_plans: add separate grade tracking per type
    hp_cols = [row[1] for row in db.execute("PRAGMA table_info(homework_plans)").fetchall()]
    if "recognition_grade" not in hp_cols:
        db.execute("ALTER TABLE homework_plans ADD COLUMN recognition_grade TEXT NOT NULL DEFAULT ''")
        db.execute("ALTER TABLE homework_plans ADD COLUMN writing_grade TEXT NOT NULL DEFAULT ''")
        # Backfill: copy existing grade to both recognition_grade and writing_grade
        db.execute("UPDATE homework_plans SET recognition_grade = grade, writing_grade = grade")
    db.commit()
    db.close()


def hash_password(password, salt=None):
    if salt is None:
        salt = os.urandom(16).hex()
    hashed = hashlib.sha256((salt + password).encode()).hexdigest()
    return f"{salt}:{hashed}"


def verify_password(password, stored):
    salt, _ = stored.split(":")
    return hash_password(password, salt) == stored


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
        return {
            "mode": mode,
            "question": correct["char"],
            "options": options,
            "correct_index": options.index(correct["pinyin"]),
            "answer": correct["pinyin"],
            "word_hint": "、".join(correct["words"]),
        }

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
            "word_hint": "、".join(correct["words"]),
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
            "word_hint": "、".join(correct["words"]),
        }

    if mode == "pinyin_typing":
        # Show character, handwrite pinyin
        q = {
            "mode": mode,
            "question": correct["char"],
            "answer": correct["pinyin"],
            "word_hint": "、".join(correct["words"]),
            "display_char": correct["char"],
            "display_pinyin": correct["pinyin"],
        }
        if correct["char"] in MULTI_PINYIN:
            cw = ""
            # Search grade WORDS for a context word
            for w in WORDS.get(grade, []):
                syllables = w["pinyin"].split()
                if len(w["word"]) == len(syllables):
                    for ch, py in zip(w["word"], syllables):
                        if ch == correct["char"] and py == correct["pinyin"]:
                            cw = w["word"]
                            break
                if cw:
                    break
            if not cw and correct["words"]:
                cw = correct["words"][0]
            if cw:
                q["context_word"] = cw
        return q

    if mode == "dictation_handwrite":
        word_list = WORDS.get(grade, [])
        # Only pick multi-character words (词语), exclude single characters (识字表)
        ciyu_list = [w for w in word_list if len(w["word"]) >= 2]
        if not ciyu_list:
            return {"error": "该年级暂无词语数据"}
        word_entry = random.choice(ciyu_list)
        return {
            "mode": mode,
            "question": word_entry["pinyin"],
            "answer": word_entry["word"],
        }

    return {"error": f"Unknown mode: {mode}"}


def _pick_distractors(correct: dict, others: list, key: str, count: int = 3,
                      exclude_homophones: bool = False) -> list:
    """Pick distractor options that differ from the correct answer."""
    correct_val = correct[key]
    candidates = [c for c in others if c[key] != correct_val]

    if exclude_homophones:
        # Remove characters whose pinyin matches the correct answer exactly
        candidates = [c for c in candidates if c["pinyin"] != correct["pinyin"]]
    elif key == "char":
        # Prefer characters with similar pinyin (same base syllable) for harder questions
        base = _strip_tone(correct["pinyin"])
        similar = [c for c in candidates if _strip_tone(c["pinyin"]) == base]
        if len(similar) >= count:
            return random.sample(similar, count)

    if len(candidates) < count:
        fallback = [c for c in others if c[key] != correct_val]
        if exclude_homophones:
            fallback = [c for c in fallback if c["pinyin"] != correct["pinyin"]]
        candidates = fallback

    if len(candidates) < count:
        return random.sample(candidates, len(candidates)) if candidates else []

    return random.sample(candidates, count)


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
        word_entry = random.choice(ciyu_entries)
        return {
            "mode": mode,
            "question": word_entry["pinyin"],
            "answer": word_entry["word"],
        }

    # For char modes, convert 识字 entries to CHARACTERS-compatible format
    if not shizi_entries:
        return {"error": "该课/单元暂无识字数据"}

    # Build char_list with {char, pinyin, words} format
    char_list = []
    for e in shizi_entries:
        char_list.append({
            "char": e["word"], "pinyin": e["pinyin"], "words": [],
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
        return {
            "mode": mode, "question": correct["char"], "options": options,
            "correct_index": options.index(correct["pinyin"]),
            "answer": correct["pinyin"],
            "word_hint": "、".join(correct["words"]),
        }

    if mode == "pinyin_to_char":
        distractors = _pick_distractors(correct, distractor_pool, key="char")
        options = [correct["char"]] + [d["char"] for d in distractors]
        random.shuffle(options)
        return {
            "mode": mode, "question": correct["pinyin"], "options": options,
            "correct_index": options.index(correct["char"]),
            "answer": correct["char"],
            "word_hint": "、".join(correct["words"]),
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
            "word_hint": "、".join(correct["words"]),
        }

    return {"error": f"Unknown mode: {mode}"}


@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/register", methods=["POST"])
def register():
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
    existing = db.execute("SELECT id FROM users WHERE username = ?", (username,)).fetchone()
    if existing:
        return jsonify({"error": "用户名已存在"}), 409

    pw_hash = hash_password(password)
    cursor = db.execute("INSERT INTO users (username, password_hash) VALUES (?, ?)", (username, pw_hash))
    db.commit()

    session["user_id"] = cursor.lastrowid
    session["username"] = username
    return jsonify({"username": username})


@app.route("/api/login", methods=["POST"])
def login():
    data = request.get_json()
    username = (data.get("username") or "").strip()
    password = data.get("password") or ""

    if not username or not password:
        return jsonify({"error": "用户名和密码不能为空"}), 400

    db = get_db()
    user = db.execute("SELECT * FROM users WHERE username = ?", (username,)).fetchone()
    if not user or not verify_password(password, user["password_hash"]):
        return jsonify({"error": "用户名或密码错误"}), 401

    session["user_id"] = user["id"]
    session["username"] = username
    return jsonify({"username": username})


@app.route("/api/logout", methods=["POST"])
def logout():
    session.clear()
    return jsonify({"ok": True})


@app.route("/api/me")
def me():
    if "user_id" not in session:
        return jsonify({"logged_in": False})
    return jsonify({"logged_in": True, "username": session["username"]})


@app.route("/api/scores", methods=["GET", "POST"])
def scores_api():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    if request.method == "POST":
        data = request.get_json()
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
        db.execute(
            "INSERT INTO scores (user_id, grade, mode, score, combo_max, total_questions, correct_answers) VALUES (?, ?, ?, ?, ?, ?, ?)",
            (session["user_id"], grade, mode, score, combo_max, total_questions, correct_answers),
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
           FROM scores WHERE user_id = ?
           GROUP BY DATE(created_at)""",
        (session["user_id"],),
    ).fetchall()
    hw_rows = db.execute(
        """SELECT date,
                  SUM(total_questions) as total_questions,
                  SUM(correct_answers) as correct_answers,
                  0 as score
           FROM daily_assignments WHERE user_id = ? AND status = 'completed'
           GROUP BY date""",
        (session["user_id"],),
    ).fetchall()

    # Merge by date
    merged = {}
    for r in game_rows:
        d = r["date"]
        merged[d] = {"date": d, "total_questions": r["total_questions"], "correct_answers": r["correct_answers"], "score": r["score"], "source": "游戏"}
    for r in hw_rows:
        d = r["date"]
        if d in merged:
            merged[d]["total_questions"] += r["total_questions"]
            merged[d]["correct_answers"] += r["correct_answers"]
            merged[d]["source"] = "游戏+作业"
        else:
            merged[d] = {"date": d, "total_questions": r["total_questions"], "correct_answers": r["correct_answers"], "score": 0, "source": "作业"}

    wrong_counts = {}
    for r in db.execute(
        "SELECT DATE(created_at) as date, COUNT(DISTINCT character) as cnt FROM wrong_answers WHERE user_id = ? GROUP BY DATE(created_at)",
        (session["user_id"],),
    ).fetchall():
        wrong_counts[r["date"]] = r["cnt"]

    scores = []
    for d in sorted(merged.keys(), reverse=True)[:60]:
        entry = merged[d]
        entry["wrong_count"] = wrong_counts.get(d, 0)
        scores.append(entry)
    return jsonify({"scores": scores})


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
        data = request.get_json()
        db = get_db()
        db.execute(
            "INSERT INTO wrong_answers (user_id, character, pinyin, words, grade, mode) VALUES (?, ?, ?, ?, ?, ?)",
            (session["user_id"], data["character"], data["pinyin"], data["words"], data["grade"], data["mode"]),
        )
        db.commit()
        return jsonify({"ok": True})

    date = request.args.get("date")
    db = get_db()
    if date:
        rows = db.execute(
            "SELECT character, pinyin, words, grade, mode, review_count, DATE(created_at) as date FROM wrong_answers WHERE user_id = ? AND DATE(created_at) = ? GROUP BY character, mode ORDER BY review_count ASC, created_at",
            (session["user_id"], date),
        ).fetchall()
    else:
        rows = db.execute(
            "SELECT character, pinyin, words, grade, mode, review_count, DATE(created_at) as date FROM wrong_answers WHERE user_id = ? GROUP BY character, mode ORDER BY review_count ASC, created_at DESC",
            (session["user_id"],),
        ).fetchall()
    return jsonify({"wrong_answers": [dict(r) for r in rows]})


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

    char_list = CHARACTERS.get(grade, [])
    if len(char_list) < 4:
        return jsonify({"error": "年级数据不足"}), 400

    # Build a "correct" entry compatible with _pick_distractors
    correct = {"char": character, "pinyin": pinyin, "words": words.split("、") if words else []}
    others = [c for c in char_list if c["char"] != character]

    if mode == "char_to_pinyin":
        distractors = _pick_distractors(correct, others, key="pinyin")
        options = [pinyin] + [d["pinyin"] for d in distractors]
        random.shuffle(options)
        return jsonify({
            "mode": mode, "question": character, "options": options,
            "correct_index": options.index(pinyin),
            "answer": pinyin, "word_hint": words,
        })

    if mode == "pinyin_to_char":
        distractors = _pick_distractors(correct, others, key="char")
        options = [character] + [d["char"] for d in distractors]
        random.shuffle(options)
        return jsonify({
            "mode": mode, "question": pinyin, "options": options,
            "correct_index": options.index(character),
            "answer": character, "word_hint": words,
        })

    if mode == "listen_to_char":
        distractors = _pick_distractors(correct, others, key="char", exclude_homophones=True)
        options = [character] + [d["char"] for d in distractors]
        random.shuffle(options)
        return jsonify({
            "mode": mode, "question": character, "question_pinyin": pinyin,
            "options": options, "correct_index": options.index(character),
            "answer": character, "word_hint": words,
        })

    if mode == "dictation_handwrite":
        return jsonify({
            "mode": mode, "question": pinyin, "answer": character,
        })

    return jsonify({"error": f"Unknown mode: {mode}"}), 400


@app.route("/api/review_done", methods=["POST"])
def review_done():
    """Increment review_count for a wrong answer. Move to mastered if count >= 3."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    data = request.get_json()
    character = data.get("character", "")
    mode = data.get("mode", "")
    db = get_db()

    db.execute(
        "UPDATE wrong_answers SET review_count = review_count + 1 WHERE user_id = ? AND character = ? AND mode = ?",
        (session["user_id"], character, mode),
    )
    db.commit()

    # Check if any rows now have review_count >= 3 — move to mastered
    rows = db.execute(
        "SELECT * FROM wrong_answers WHERE user_id = ? AND character = ? AND mode = ? AND review_count >= 3",
        (session["user_id"], character, mode),
    ).fetchall()

    mastered = False
    for r in rows:
        db.execute(
            "INSERT INTO mastered_words (user_id, character, pinyin, words, grade, mode, review_count, created_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            (r["user_id"], r["character"], r["pinyin"], r["words"], r["grade"], r["mode"], r["review_count"], r["created_at"]),
        )
        mastered = True

    if mastered:
        db.execute(
            "DELETE FROM wrong_answers WHERE user_id = ? AND character = ? AND mode = ? AND review_count >= 3",
            (session["user_id"], character, mode),
        )
        db.commit()

    return jsonify({"ok": True, "mastered": mastered})


@app.route("/api/mastered_words")
def mastered_words_api():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    rows = db.execute(
        "SELECT character, pinyin, words, grade, mode, review_count, DATE(created_at) as date, DATE(mastered_at) as mastered_date FROM mastered_words WHERE user_id = ? ORDER BY mastered_at DESC",
        (session["user_id"],),
    ).fetchall()
    return jsonify({"mastered_words": [dict(r) for r in rows]})


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
               WHERE s.mode = ?
               GROUP BY s.user_id
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
               GROUP BY s.user_id
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
    data = request.get_json()
    password = data.get("password", "")
    if password != ADMIN_PASSWORD:
        return jsonify({"error": "管理员密码错误"}), 401
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
        wa = db.execute("SELECT COUNT(*) as cnt FROM wrong_answers WHERE user_id = ?", (u["id"],)).fetchone()
        d["wrong_count"] = wa["cnt"]
        # Count mastered
        ma = db.execute("SELECT COUNT(*) as cnt FROM mastered_words WHERE user_id = ?", (u["id"],)).fetchone()
        d["mastered_count"] = ma["cnt"]
        result.append(d)

    return jsonify({"users": result})


@app.route("/api/admin/user/<int:user_id>/details")
def admin_user_details(user_id):
    """Return detailed history for a specific user."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    db = get_db()
    user = db.execute("SELECT id, username, coins, game_minutes, created_at FROM users WHERE id = ?", (user_id,)).fetchone()
    if not user:
        return jsonify({"error": "用户不存在"}), 404

    # Score history grouped by date
    scores = db.execute(
        """SELECT DATE(created_at) as date, grade, mode,
                  SUM(total_questions) as total_questions,
                  SUM(correct_answers) as correct_answers,
                  SUM(score) as score
           FROM scores WHERE user_id = ?
           GROUP BY DATE(created_at), grade, mode
           ORDER BY date DESC LIMIT 200""",
        (user_id,),
    ).fetchall()

    # Wrong answers
    wrong_answers = db.execute(
        """SELECT character, pinyin, words, grade, mode, review_count, DATE(created_at) as date
           FROM wrong_answers WHERE user_id = ?
           ORDER BY created_at DESC""",
        (user_id,),
    ).fetchall()

    # Mastered words
    mastered = db.execute(
        """SELECT character, pinyin, words, grade, mode, DATE(mastered_at) as mastered_date
           FROM mastered_words WHERE user_id = ?
           ORDER BY mastered_at DESC""",
        (user_id,),
    ).fetchall()

    return jsonify({
        "user": dict(user),
        "scores": [dict(r) for r in scores],
        "wrong_answers": [dict(r) for r in wrong_answers],
        "mastered": [dict(r) for r in mastered],
    })


@app.route("/admin/user/<int:user_id>/wrong")
def admin_user_wrong_page(user_id):
    """Full-page view of a user's wrong answers (admin only)."""
    if not session.get("is_admin"):
        return redirect(url_for("index"))
    db = get_db()
    user = db.execute("SELECT username FROM users WHERE id = ?", (user_id,)).fetchone()
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
            db.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('coin_rules', ?)",
                       (json.dumps(rules, ensure_ascii=False),))

        if "exchange_packages" in data:
            pkgs = data["exchange_packages"]
            if not isinstance(pkgs, list):
                return jsonify({"error": "兑换套餐格式错误"}), 400
            for p in pkgs:
                if not isinstance(p.get("price"), int) or not isinstance(p.get("minutes"), int):
                    return jsonify({"error": "套餐格式错误: 需要 price 和 minutes 为整数"}), 400
            db.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('exchange_packages', ?)",
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
    row = db.execute("SELECT coins, game_minutes, recognition_streak, writing_streak FROM users WHERE id = ?",
                     (session["user_id"],)).fetchone()
    return jsonify({
        "coins": row["coins"] if row else 0,
        "game_minutes": row["game_minutes"] if row else 0,
        "recognition_streak": row["recognition_streak"] if row else 0,
        "writing_streak": row["writing_streak"] if row else 0,
    })


def _check_coin_eligible(db, user_id, mode, game_grade):
    """Check if a game at given grade is eligible for coin awards.

    Anti-cheating: prevent farming easy levels.
    - Writing (写字): max 4 books back from current homework level
    - All other modes (认字/听音等): max 2 books back from current homework level
    Returns True if coins should be awarded.
    """
    if not game_grade:
        return True  # homework mode, no grade check needed

    is_writing = mode == "dictation_handwrite"

    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
        (user_id,),
    ).fetchone()
    if not plan:
        return True  # no homework plan, allow freely

    if is_writing:
        hw_grade = plan["writing_grade"] or plan["grade"]
        max_books_back = 4
    else:
        hw_grade = plan["recognition_grade"] or plan["grade"]
        max_books_back = 2

    hw_idx = GRADE_ORDER.index(hw_grade) if hw_grade in GRADE_ORDER else 0
    game_idx = GRADE_ORDER.index(game_grade) if game_grade in GRADE_ORDER else 0
    # game_grade must be within max_books_back of hw_grade
    return game_idx >= hw_idx - max_books_back


@app.route("/api/coin-eligible")
def coin_eligible_check():
    """Check if a game mode + grade combination is eligible for coin awards."""
    if "user_id" not in session:
        return jsonify({"eligible": True})
    mode = request.args.get("mode", "")
    grade = request.args.get("grade", "")
    db = get_db()
    eligible = _check_coin_eligible(db, session["user_id"], mode, grade)
    return jsonify({"eligible": eligible})


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
    is_writing = mode == "dictation_handwrite"
    streak_col = "writing_streak" if is_writing else "recognition_streak"
    awarded_col = "writing_coins_awarded" if is_writing else "recognition_coins_awarded"

    db = get_db()
    user = db.execute(f"SELECT {streak_col}, {awarded_col}, coins FROM users WHERE id = ?",
                      (session["user_id"],)).fetchone()
    if not user:
        return jsonify({"error": "用户不存在"}), 404

    # Check if this game grade is eligible for coin awards
    coin_eligible = _check_coin_eligible(db, session["user_id"], mode, game_grade)

    coins_earned = 0
    if correct:
        new_streak = user[streak_col] + 1
        if coin_eligible:
            total_coins_at_streak = calc_streak_coins(new_streak, is_writing, db)
            coins_earned = total_coins_at_streak - user[awarded_col]
            if coins_earned > 0:
                db.execute(f"UPDATE users SET {streak_col} = ?, {awarded_col} = ?, coins = coins + ? WHERE id = ?",
                           (new_streak, total_coins_at_streak, coins_earned, session["user_id"]))
            else:
                db.execute(f"UPDATE users SET {streak_col} = ? WHERE id = ?",
                           (new_streak, session["user_id"]))
        else:
            # Still update streak display but no coins
            db.execute(f"UPDATE users SET {streak_col} = ? WHERE id = ?",
                       (new_streak, session["user_id"]))
    else:
        new_streak = 0
        db.execute(f"UPDATE users SET {streak_col} = 0, {awarded_col} = 0 WHERE id = ?",
                   (session["user_id"],))

    db.commit()
    return jsonify({
        "streak": new_streak,
        "coins_earned": coins_earned,
        "coins": user["coins"] + coins_earned,
        "coin_eligible": coin_eligible,
    })


@app.route("/api/shop")
def shop_api():
    db = get_db()
    packages = _get_exchange_packages(db)
    rules = _get_coin_rules(db)
    return jsonify({"items": packages, "coin_rules": rules})


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

    user = db.execute("SELECT coins, game_minutes FROM users WHERE id = ?", (session["user_id"],)).fetchone()
    if user["coins"] < package["price"]:
        return jsonify({"error": "金币不足"}), 400

    db.execute("UPDATE users SET coins = coins - ?, game_minutes = game_minutes + ? WHERE id = ?",
               (package["price"], package["minutes"], session["user_id"]))
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

    # Find active homework plan
    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
        (user_id,),
    ).fetchone()
    if not plan:
        existing = db.execute(
            "SELECT * FROM daily_assignments WHERE user_id = ? AND date = ?",
            (user_id, today),
        ).fetchall()
        return [dict(r) for r in existing]

    existing = db.execute(
        "SELECT * FROM daily_assignments WHERE user_id = ? AND date = ?",
        (user_id, today),
    ).fetchall()

    if not existing:
        # First visit today: create initial assignments using cross-grade search
        rec_base_grade = plan["recognition_grade"] or plan["grade"]
        wrt_base_grade = plan["writing_grade"] or plan["grade"]
        rec_grade, rec_ln = find_next_lesson_across_grades(
            rec_base_grade, plan["recognition_lesson"], "识字")
        wrt_grade, wrt_ln = find_next_lesson_across_grades(
            wrt_base_grade, plan["writing_lesson"], "词语")
        if rec_grade and rec_ln:
            db.execute(
                "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num) VALUES (?, ?, 'recognition', ?, ?)",
                (user_id, today, rec_grade, rec_ln),
            )
        if wrt_grade and wrt_ln:
            db.execute(
                "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num) VALUES (?, ?, 'writing', ?, ?)",
                (user_id, today, wrt_grade, wrt_ln),
            )
        db.commit()
    else:
        # Auto-create next lesson for each type if all of that type are completed
        changed = False
        for hw_type, content_key in [("recognition", "识字"), ("writing", "词语")]:
            type_assignments = [dict(r) for r in existing if r["type"] == hw_type]
            if not type_assignments:
                continue
            has_pending = any(a["status"] == "pending" for a in type_assignments)
            if has_pending:
                continue
            # All completed — find next using cross-grade search
            plan_lesson = plan["recognition_lesson"] if hw_type == "recognition" else plan["writing_lesson"]
            base_grade = (plan["recognition_grade"] if hw_type == "recognition" else plan["writing_grade"]) or plan["grade"]
            next_grade, next_ln = find_next_lesson_across_grades(
                base_grade, plan_lesson, content_key)
            if not next_grade:
                continue
            # Avoid duplicate
            dup = any(a["grade"] == next_grade and a["lesson_num"] == next_ln for a in type_assignments)
            if dup:
                continue
            db.execute(
                "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num) VALUES (?, ?, ?, ?, ?)",
                (user_id, today, hw_type, next_grade, next_ln),
            )
            changed = True
        if changed:
            db.commit()

    rows = db.execute(
        "SELECT * FROM daily_assignments WHERE user_id = ? AND date = ?",
        (user_id, today),
    ).fetchall()
    return [dict(r) for r in rows]


@app.route("/api/homework/today")
def homework_today():
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    assignments = _get_or_create_today_assignments(db, session["user_id"])
    # Also get plan info
    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
        (session["user_id"],),
    ).fetchone()
    plan_info = None
    if plan:
        rec_grade = plan["recognition_grade"] or plan["grade"]
        wrt_grade = plan["writing_grade"] or plan["grade"]
        rec_total = len(HOMEWORK_LESSONS.get(rec_grade, {}))
        wrt_total = len(HOMEWORK_LESSONS.get(wrt_grade, {}))
        plan_info = {
            "grade": plan["grade"],
            "grade_short": grade_short_name(plan["grade"]),
            "recognition_grade": rec_grade,
            "writing_grade": wrt_grade,
            "recognition_lesson": plan["recognition_lesson"],
            "writing_lesson": plan["writing_lesson"],
            "rec_total_lessons": rec_total,
            "wrt_total_lessons": wrt_total,
            "total_lessons": max(rec_total, wrt_total),
        }
    # Check if there are wrong answers from previous days needing review
    today = date.today().isoformat()
    review_items = db.execute(
        """SELECT character, pinyin, words, grade, mode, review_count
           FROM wrong_answers
           WHERE user_id = ? AND DATE(created_at) < ?
           GROUP BY character, mode
           ORDER BY review_count ASC, created_at DESC""",
        (session["user_id"], today),
    ).fetchall()
    review_needed = [dict(r) for r in review_items]

    return jsonify({
        "assignments": assignments,
        "plan": plan_info,
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
    for item in items:
        character = item.get("character", "")
        mode = item.get("mode", "")
        db.execute(
            "UPDATE wrong_answers SET review_count = review_count + 1 WHERE user_id = ? AND character = ? AND mode = ?",
            (session["user_id"], character, mode),
        )
        # Delete if reviewed enough (>= 3)
        db.execute(
            "DELETE FROM wrong_answers WHERE user_id = ? AND character = ? AND mode = ? AND review_count >= 3",
            (session["user_id"], character, mode),
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
        "SELECT * FROM daily_assignments WHERE id = ? AND user_id = ?",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    grade = assignment["grade"]
    lesson_num = assignment["lesson_num"]
    hw_type = assignment["type"]

    lessons = HOMEWORK_LESSONS.get(grade, {})
    lesson_data = lessons.get(lesson_num, {})

    questions = []
    if hw_type == "recognition":
        # Use combined 认字 pool (识字表 + 写字表)
        entries = lesson_data.get("认字", []) or lesson_data.get("识字", [])
        if not entries:
            return jsonify({"error": "该课暂无识字数据"}), 400
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
                context_word = _find_context_word(
                    char_text, entry["pinyin"], grade, lesson_num)
            # Recognition homework uses pinyin typing mode (给汉字注音)
            q = {
                "mode": "pinyin_typing",
                "question": entry["word"],
                "answer": entry["pinyin"],
                "word_hint": "、".join(word_hint_list),
                "display_char": entry["word"],
                "display_pinyin": entry["pinyin"],
            }
            if context_word:
                q["context_word"] = context_word
            questions.append(q)
        random.shuffle(questions)
    elif hw_type == "writing":
        entries = lesson_data.get("词语", [])
        if not entries:
            return jsonify({"error": "该课暂无词语数据"}), 400
        for entry in entries:
            questions.append({
                "mode": "dictation_handwrite",
                "question": entry["pinyin"],
                "answer": entry["word"],
                "display_char": entry["word"], "display_pinyin": entry["pinyin"],
            })
        random.shuffle(questions)

    return jsonify({
        "assignment_id": assignment_id,
        "type": hw_type,
        "grade": grade,
        "lesson_num": lesson_num,
        "questions": questions,
        "total": len(questions),
    })


@app.route("/api/homework/preview/<int:assignment_id>")
def homework_preview(assignment_id):
    """Generate preview (预习) questions for a homework assignment.
    Supports modes: char_to_pinyin, pinyin_to_char, listen_to_char."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401
    db = get_db()
    assignment = db.execute(
        "SELECT * FROM daily_assignments WHERE id = ? AND user_id = ?",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    grade = assignment["grade"]
    lesson_num = assignment["lesson_num"]
    mode = request.args.get("mode", "char_to_pinyin")
    if mode not in ("char_to_pinyin", "pinyin_to_char", "listen_to_char"):
        mode = "char_to_pinyin"

    lessons = HOMEWORK_LESSONS.get(grade, {})
    lesson_data = lessons.get(lesson_num, {})

    # Build preview questions from 认字 pool
    entries = lesson_data.get("认字", []) or lesson_data.get("识字", [])
    if not entries:
        return jsonify({"error": "该课暂无数据"}), 400

    all_chars = CHARACTERS.get(grade, [])
    questions = []
    for entry in entries:
        # Only single characters for game modes (multi-char words don't work well for selection)
        if len(entry["word"]) > 1:
            continue
        correct = {"char": entry["word"], "pinyin": entry["pinyin"], "words": []}
        for c in all_chars:
            if c["char"] == entry["word"]:
                correct["words"] = c.get("words", [])
                break
        others = [c for c in all_chars if c["char"] != correct["char"]]

        if mode == "char_to_pinyin":
            distractors = _pick_distractors(correct, others, key="pinyin")
            options = [correct["pinyin"]] + [d["pinyin"] for d in distractors]
            random.shuffle(options)
            questions.append({
                "mode": mode, "question": correct["char"],
                "options": options, "correct_index": options.index(correct["pinyin"]),
                "answer": correct["pinyin"],
                "word_hint": "、".join(correct["words"]),
                "display_char": correct["char"], "display_pinyin": correct["pinyin"],
            })
        elif mode == "pinyin_to_char":
            distractors = _pick_distractors(correct, others, key="char")
            options = [correct["char"]] + [d["char"] for d in distractors]
            random.shuffle(options)
            questions.append({
                "mode": mode, "question": correct["pinyin"],
                "options": options, "correct_index": options.index(correct["char"]),
                "answer": correct["char"],
                "word_hint": "、".join(correct["words"]),
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
                "word_hint": "、".join(correct["words"]),
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
    time_spent = data.get("time_spent", 0)
    wrong_items = json.dumps(data.get("wrong_items", []), ensure_ascii=False)

    db = get_db()
    assignment = db.execute(
        "SELECT * FROM daily_assignments WHERE id = ? AND user_id = ?",
        (assignment_id, session["user_id"]),
    ).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    # Update assignment
    db.execute(
        """UPDATE daily_assignments
           SET status = 'completed', total_questions = ?, correct_answers = ?,
               time_spent = ?, wrong_items = ?, completed_at = CURRENT_TIMESTAMP
           WHERE id = ?""",
        (total_questions, correct_answers, time_spent, wrong_items, assignment_id),
    )

    # Advance lesson if this assignment was completed (not a repeat)
    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
        (session["user_id"],),
    ).fetchone()
    if plan and assignment["status"] == "pending":
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
                db.execute("UPDATE homework_plans SET recognition_lesson = ?, recognition_grade = ? WHERE id = ?",
                           (next_ln, next_grade, plan["id"]))
            else:
                db.execute("UPDATE homework_plans SET writing_lesson = ?, writing_grade = ? WHERE id = ?",
                           (next_ln, next_grade, plan["id"]))

    # Also record wrong answers in the main wrong_answers table
    for item in data.get("wrong_items", []):
        db.execute(
            "INSERT INTO wrong_answers (user_id, character, pinyin, words, grade, mode) VALUES (?, ?, ?, ?, ?, ?)",
            (session["user_id"], item.get("character", ""), item.get("pinyin", ""),
             item.get("words", ""), assignment["grade"], item.get("mode", "")),
        )

    # Coins are now awarded in real-time via /api/streak during the quiz
    coins_earned = 0

    # Auto-create next lesson assignment if this was first completion
    next_assignment = None
    if plan and assignment["status"] == "pending":
        today = date.today().isoformat()
        # Re-read the updated plan to get the advanced grade/lesson
        updated_plan = db.execute(
            "SELECT * FROM homework_plans WHERE id = ?", (plan["id"],)
        ).fetchone()
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
                "SELECT id FROM daily_assignments WHERE user_id = ? AND date = ? AND type = ? AND grade = ? AND lesson_num = ?",
                (session["user_id"], today, assignment["type"], next_grade, next_lesson),
            ).fetchone()
            if not dup:
                cur = db.execute(
                    "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num) VALUES (?, ?, ?, ?, ?)",
                    (session["user_id"], today, assignment["type"], next_grade, next_lesson),
                )
                next_assignment = {
                    "id": cur.lastrowid,
                    "type": assignment["type"],
                    "grade": next_grade,
                    "lesson_num": next_lesson,
                }

    db.commit()

    # Check if both assignments for today are completed
    today = date.today().isoformat()
    pending = db.execute(
        "SELECT COUNT(*) as cnt FROM daily_assignments WHERE user_id = ? AND date = ? AND status != 'completed'",
        (session["user_id"], today),
    ).fetchone()

    all_done = pending["cnt"] == 0

    return jsonify({"ok": True, "coins_earned": coins_earned, "all_done": all_done, "next_assignment": next_assignment})


@app.route("/api/homework/progress")
def homework_progress():
    """Get homework progress for all grades."""
    if "user_id" not in session:
        return jsonify({"error": "未登录"}), 401

    db = get_db()
    plans = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = ? ORDER BY id",
        (session["user_id"],),
    ).fetchall()

    progress = []
    for p in plans:
        rec_grade = p["recognition_grade"] or p["grade"]
        wrt_grade = p["writing_grade"] or p["grade"]
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
        })

    # Also include recent history (last 7 days)
    week_ago = (date.today() - timedelta(days=7)).isoformat()
    history = db.execute(
        """SELECT date, type, grade, lesson_num, status, total_questions, correct_answers, time_spent
           FROM daily_assignments WHERE user_id = ? AND date >= ?
           ORDER BY date DESC, type""",
        (session["user_id"], week_ago),
    ).fetchall()

    return jsonify({"progress": progress, "history": [dict(r) for r in history]})


# --- Admin Homework Routes ---

@app.route("/api/admin/homework/plan", methods=["POST"])
def admin_homework_plan():
    """Create or update a homework plan for a user."""
    if not session.get("is_admin"):
        return jsonify({"error": "无管理员权限"}), 403

    data = request.get_json(force=True, silent=True)
    if not data:
        return jsonify({"error": "无效的请求数据"}), 400
    user_id = data.get("user_id")
    grade = data.get("grade", "")
    rec_lesson = data.get("recognition_lesson", 1)
    wrt_lesson = data.get("writing_lesson", 1)

    if grade not in HOMEWORK_LESSONS:
        return jsonify({"error": f"无效年级: {grade}"}), 400

    db = get_db()
    # Deactivate existing plans for this user
    db.execute("UPDATE homework_plans SET active = 0 WHERE user_id = ?", (user_id,))
    # Delete today's pending assignments so new plan takes effect immediately
    today = date.today().isoformat()
    db.execute(
        "DELETE FROM daily_assignments WHERE user_id = ? AND date = ? AND status = 'pending'",
        (user_id, today),
    )
    # Create new plan with separate grade tracking for each type
    db.execute(
        "INSERT INTO homework_plans (user_id, grade, recognition_lesson, writing_lesson, recognition_grade, writing_grade) VALUES (?, ?, ?, ?, ?, ?)",
        (user_id, grade, rec_lesson, wrt_lesson, grade, grade),
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
    assignment = db.execute("SELECT * FROM daily_assignments WHERE id = ?", (assignment_id,)).fetchone()
    if not assignment:
        return jsonify({"error": "作业不存在"}), 404

    # Create repeat for tomorrow
    tomorrow = (date.today() + timedelta(days=1)).isoformat()
    # Remove any existing assignment of same type for tomorrow
    db.execute(
        "DELETE FROM daily_assignments WHERE user_id = ? AND date = ? AND type = ?",
        (assignment["user_id"], tomorrow, assignment["type"]),
    )
    db.execute(
        "INSERT INTO daily_assignments (user_id, date, type, grade, lesson_num) VALUES (?, ?, ?, ?, ?)",
        (assignment["user_id"], tomorrow, assignment["type"], assignment["grade"], assignment["lesson_num"]),
    )
    # Roll back the lesson advancement
    plan = db.execute(
        "SELECT * FROM homework_plans WHERE user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
        (assignment["user_id"],),
    ).fetchone()
    if plan:
        if assignment["type"] == "recognition":
            db.execute(
                "UPDATE homework_plans SET recognition_lesson = ?, recognition_grade = ? WHERE id = ?",
                (assignment["lesson_num"], assignment["grade"], plan["id"]),
            )
        else:
            db.execute(
                "UPDATE homework_plans SET writing_lesson = ?, writing_grade = ? WHERE id = ?",
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
        plan = db.execute(
            "SELECT * FROM homework_plans WHERE user_id = ? AND active = 1 ORDER BY id DESC LIMIT 1",
            (u["id"],),
        ).fetchone()
        if not plan:
            continue

        assignments = db.execute(
            "SELECT * FROM daily_assignments WHERE user_id = ? AND date = ? ORDER BY type",
            (u["id"], today),
        ).fetchall()

        rec_grade = plan["recognition_grade"] or plan["grade"]
        wrt_grade = plan["writing_grade"] or plan["grade"]
        rec_total = len(HOMEWORK_LESSONS.get(rec_grade, {}))
        wrt_total = len(HOMEWORK_LESSONS.get(wrt_grade, {}))
        result.append({
            "user_id": u["id"],
            "username": u["username"],
            "grade": plan["grade"],
            "grade_short": grade_short_name(plan["grade"]),
            "recognition_grade": rec_grade,
            "writing_grade": wrt_grade,
            "recognition_lesson": plan["recognition_lesson"],
            "writing_lesson": plan["writing_lesson"],
            "rec_total_lessons": rec_total,
            "wrt_total_lessons": wrt_total,
            "total_lessons": max(rec_total, wrt_total),
            "today_assignments": [dict(a) for a in assignments],
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
           FROM daily_assignments WHERE user_id = ? AND date >= ?
           ORDER BY date DESC, type""",
        (user_id, start_date),
    ).fetchall()

    # Game session records (scores)
    game_rows = db.execute(
        """SELECT DATE(created_at) as date, grade, mode, total_questions, correct_answers, score
           FROM scores WHERE user_id = ? AND DATE(created_at) >= ?
           ORDER BY created_at DESC""",
        (user_id, start_date),
    ).fetchall()

    # Group by date
    daily_log = {}
    for row in hw_rows:
        d = row["date"]
        if d not in daily_log:
            daily_log[d] = {"date": d, "homework": [], "games": []}
        daily_log[d]["homework"].append(dict(row))

    for row in game_rows:
        d = row["date"]
        if d not in daily_log:
            daily_log[d] = {"date": d, "homework": [], "games": []}
        daily_log[d]["games"].append(dict(row))

    # Sort by date descending
    result = sorted(daily_log.values(), key=lambda x: x["date"], reverse=True)
    return jsonify({"daily_log": result})


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


if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=5001)
