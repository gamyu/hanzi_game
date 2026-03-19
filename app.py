import hashlib
import json
import os
import random
import sqlite3
import urllib.request
from flask import Flask, g, jsonify, render_template, request, session
from characters import CHARACTERS
from words import WORDS

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
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
    """)
    # Migrate: add columns if missing
    cols = [row[1] for row in db.execute("PRAGMA table_info(scores)").fetchall()]
    if "total_questions" not in cols:
        db.execute("ALTER TABLE scores ADD COLUMN total_questions INTEGER NOT NULL DEFAULT 0")
    if "correct_answers" not in cols:
        db.execute("ALTER TABLE scores ADD COLUMN correct_answers INTEGER NOT NULL DEFAULT 0")
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
        return render_template("index.html")
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
            "SELECT DISTINCT character, pinyin, words, grade FROM wrong_answers WHERE user_id = ? AND DATE(created_at) = ? ORDER BY created_at",
            (session["user_id"], date),
        ).fetchall()
    else:
        rows = db.execute(
            "SELECT DISTINCT character, pinyin, words, grade, DATE(created_at) as date FROM wrong_answers WHERE user_id = ? ORDER BY created_at DESC",
            (session["user_id"],),
        ).fetchall()
    return jsonify({"wrong_answers": [dict(r) for r in rows]})


@app.route("/review")
def review_page():
    if "user_id" not in session:
        return render_template("index.html")
    return render_template("review.html", username=session["username"])


@app.route("/api/grades")
def grades():
    grade_list = list(CHARACTERS.keys())
    return jsonify({"grades": grade_list})


@app.route("/api/question")
def question():
    grade = request.args.get("grade", "一年级上")
    mode = request.args.get("mode", "char_to_pinyin")

    if grade not in CHARACTERS:
        return jsonify({"error": f"Unknown grade: {grade}"}), 400

    result = _generate_question(grade, mode)
    if "error" in result:
        return jsonify(result), 400

    return jsonify(result)


if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=5001)
