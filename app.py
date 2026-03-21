import asyncio
import hashlib
import io
import json
import os
import random
import sqlite3
import urllib.request

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

    # Define unit mapping (四年级下册 统编版)
    UNIT_MAP["四年级下"] = {
        "第一单元": [1, 2, 3, 4],
        "第二单元": [5, 6, 7, 8],
        "第三单元": [9, 10, 11],
        "第四单元": [12, 13, 14, 15],
        "第五单元": [16, 17],
        "第六单元": [18, 19, 20],
        "第七单元": [21, 22, 23, 24],
        "第八单元": [25, 26, 27, 28],
    }


_build_lesson_data()

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", os.urandom(32))

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
    # Migrate: add columns if missing
    cols = [row[1] for row in db.execute("PRAGMA table_info(scores)").fetchall()]
    if "total_questions" not in cols:
        db.execute("ALTER TABLE scores ADD COLUMN total_questions INTEGER NOT NULL DEFAULT 0")
    if "correct_answers" not in cols:
        db.execute("ALTER TABLE scores ADD COLUMN correct_answers INTEGER NOT NULL DEFAULT 0")
    wa_cols = [row[1] for row in db.execute("PRAGMA table_info(wrong_answers)").fetchall()]
    if "review_count" not in wa_cols:
        db.execute("ALTER TABLE wrong_answers ADD COLUMN review_count INTEGER NOT NULL DEFAULT 0")
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

    if mode == "dictation_handwrite":
        word_list = WORDS.get(grade, [])
        if not word_list:
            return {"error": "该年级暂无词语数据"}
        word_entry = random.choice(word_list)
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
    rows = db.execute(
        """SELECT DATE(created_at) as date,
                  SUM(total_questions) as total_questions,
                  SUM(correct_answers) as correct_answers,
                  SUM(score) as score
           FROM scores WHERE user_id = ?
           GROUP BY DATE(created_at)
           ORDER BY date DESC LIMIT 60""",
        (session["user_id"],),
    ).fetchall()
    wrong_counts = {}
    for r in db.execute(
        "SELECT DATE(created_at) as date, COUNT(DISTINCT character) as cnt FROM wrong_answers WHERE user_id = ? GROUP BY DATE(created_at)",
        (session["user_id"],),
    ).fetchall():
        wrong_counts[r["date"]] = r["cnt"]
    scores = []
    for r in rows:
        d = dict(r)
        d["wrong_count"] = wrong_counts.get(d["date"], 0)
        scores.append(d)
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
    grade_list = list(CHARACTERS.keys())
    return jsonify({"grades": grade_list})


@app.route("/api/lessons")
def lessons_api():
    """Return lesson/unit structure for a grade (if available)."""
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
