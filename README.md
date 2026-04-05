# Hanzi Game - 汉字小达人

A web-based Chinese character learning application for elementary school students, aligned with the PEP (人教版) Chinese language curriculum. It combines daily homework, interactive quizzes, and handwriting recognition to help students master character recognition, pinyin annotation, and vocabulary writing.

## Features

### Homework System (每日作业)
- **Auto-generated daily assignments** based on each student's learning plan and progress
- **Recognition homework (认字)** — handwrite pinyin annotations for characters using a four-line grid canvas
- **Writing homework (写字)** — handwrite characters from pinyin dictation
- **Multi-pronunciation support (多音字)** — context words shown in parentheses to disambiguate readings
- **Preview mode (预习)** — practice upcoming lesson vocabulary before doing homework
- **Wrong answer review** — incorrect answers must be reviewed before starting new homework
- Automatic cross-grade advancement when a grade's lessons are completed

### Game Modes (游戏模式)
- **看字选拼音** — see a character, pick the correct pinyin
- **看拼音选字** — see pinyin, pick the correct character
- **听音选字** — hear pronunciation via TTS, pick the correct character
- **给汉字注音** — see a character, handwrite its pinyin
- **看拼音写词语** — see pinyin, handwrite the compound word

### Handwriting Recognition
- Canvas-based stroke input with touch and mouse support
- Google Handwriting Recognition API integration
- Direct confirm (auto-recognize on submit) or manual recognize-then-confirm workflow

### Rewards and Progression
- Streak-based coin system with configurable milestones
- Coin shop to exchange coins for game time
- Leaderboard and score history
- Anti-cheat: coin eligibility tied to current homework level

### Administration
- Admin panel for managing homework plans, coin rules, and exchange packages
- Per-user progress tracking and wrong answer review
- Daily activity logs

## Tech Stack

- **Backend:** Python / Flask
- **Frontend:** Vanilla HTML / CSS / JavaScript
- **Database:** SQLite
- **TTS:** edge-tts
- **Handwriting:** Google Handwriting Recognition API

## Getting Started

### Prerequisites

- Python 3.10+

### Installation

```bash
git clone https://github.com/yourusername/hanzi_game.git
cd hanzi_game
pip install -r requirements.txt
```

### Running

```bash
python app.py
```

The application starts on `http://localhost:5000` by default.

### First-time Setup

1. Open the app and register a student account
2. Log in as admin (click the admin button) to set an admin password
3. Create a homework plan for the student, selecting their starting grade and lesson
4. The student can now do daily homework, preview lessons, and play quiz games

## Curriculum Data

Character and vocabulary data in `characters.py` and `words.py` covers grades 1–6 of the PEP (人教版) elementary Chinese curriculum, organized by grade and semester with lesson-level tagging.

## Author

Huan Jin

## License

This project is licensed under the Apache License 2.0 — see [LICENSE](LICENSE) for details.
