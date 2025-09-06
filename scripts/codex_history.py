#!/usr/bin/env python3
"""
Lekki dziennik historii rozmów (Codex/VS Code/Codespaces).

Zapisuje wiadomości do plików JSONL w katalogu `logs/codex_history/` (domyślnie),
z możliwością tworzenia nowych sesji, dopisywania treści i eksportu do Markdown.

Przykłady:
  - Dodaj wiadomość (user):
      python scripts/codex_history.py append --role user --text "Wiadomość"
  - Dodaj wiadomość z stdin (assistant):
      echo "Odpowiedź" | python scripts/codex_history.py capture --role assistant
  - Nowa sesja i ustaw najnowszą:
      python scripts/codex_history.py new-session
  - Lista sesji:
      python scripts/codex_history.py list-sessions
  - Eksport sesji do Markdown:
      python scripts/codex_history.py export-md --session <plik.jsonl>

Zmienne środowiskowe:
  - CODEX_HISTORY_DIR: katalog bazowy (domyślnie: logs/codex_history)
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
from pathlib import Path
import sys
import uuid


def _history_dir() -> Path:
    base = os.getenv("CODEX_HISTORY_DIR") or "logs/codex_history"
    p = Path(base)
    p.mkdir(parents=True, exist_ok=True)
    return p


def _latest_link() -> Path:
    return _history_dir() / "latest.jsonl"


def _now_iso() -> str:
    return _dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def _new_session_file() -> Path:
    ts = _dt.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    sid = uuid.uuid4().hex[:8]
    return _history_dir() / f"session-{ts}-{sid}.jsonl"


def _resolve_session(path: str | None) -> Path:
    if path:
        p = Path(path)
        if not p.is_absolute():
            p = _history_dir() / p
        return p
    # fallback do latest
    link = _latest_link()
    if link.exists():
        return link.resolve() if link.is_symlink() else link
    # brak latest -> utwórz nową sesję
    p = _new_session_file()
    p.touch()
    try:
        if _latest_link().exists() or _latest_link().is_symlink():
            _latest_link().unlink(missing_ok=True)
        _latest_link().symlink_to(p.name)
    except Exception:
        # W systemach bez symlinków – skopiuj pusty plik jako latest
        _latest_link().write_text("", encoding="utf-8")
    return p


def cmd_new_session(_args: argparse.Namespace) -> int:
    p = _new_session_file()
    p.touch()
    try:
        if _latest_link().exists() or _latest_link().is_symlink():
            _latest_link().unlink(missing_ok=True)
        _latest_link().symlink_to(p.name)
    except Exception:
        _latest_link().write_text("", encoding="utf-8")
    print(str(p))
    return 0


def _append_message(session: Path, role: str, text: str) -> None:
    rec = {
        "ts": _now_iso(),
        "role": role,
        "text": text,
    }
    with session.open("a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")


def cmd_append(args: argparse.Namespace) -> int:
    if not args.text:
        print("--text jest wymagany (albo użyj 'capture' ze stdin)", file=sys.stderr)
        return 2
    session = _resolve_session(args.session)
    _append_message(session, args.role, args.text)
    print(str(session))
    return 0


def cmd_capture(args: argparse.Namespace) -> int:
    data = sys.stdin.read()
    if not data:
        return 0
    session = _resolve_session(args.session)
    _append_message(session, args.role, data)
    print(str(session))
    return 0


def cmd_list_sessions(_args: argparse.Namespace) -> int:
    d = _history_dir()
    for p in sorted(d.glob("session-*.jsonl")):
        print(p.name)
    return 0


def cmd_export_md(args: argparse.Namespace) -> int:
    session = _resolve_session(args.session)
    if not session.exists():
        print(f"Brak pliku: {session}", file=sys.stderr)
        return 2
    lines = []
    lines.append(f"# Chat history — {session.name}")
    try:
        for line in session.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            obj = json.loads(line)
            ts = obj.get("ts", "?")
            role = obj.get("role", "?")
            text = obj.get("text", "")
            lines.append("")
            lines.append(f"## {ts} • {role}")
            lines.append("")
            lines.append("```text")
            lines.append(text)
            lines.append("```")
    except Exception as e:
        print(f"Błąd odczytu: {e}", file=sys.stderr)
        return 1
    sys.stdout.write("\n".join(lines) + "\n")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Codex chat history journal")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_new = sub.add_parser("new-session", help="Utwórz nową sesję i ustaw jako latest")
    p_new.set_defaults(func=cmd_new_session)

    p_app = sub.add_parser("append", help="Dopisz wiadomość do sesji")
    p_app.add_argument("--session", help="Plik sesji (domyślna: latest)")
    p_app.add_argument("--role", default="user", choices=["user", "assistant", "system"], help="Rola")
    p_app.add_argument("--text", help="Treść wiadomości")
    p_app.set_defaults(func=cmd_append)

    p_cap = sub.add_parser("capture", help="Dopisz wiadomość z stdin")
    p_cap.add_argument("--session", help="Plik sesji (domyślna: latest)")
    p_cap.add_argument("--role", default="assistant", choices=["user", "assistant", "system"], help="Rola")
    p_cap.set_defaults(func=cmd_capture)

    p_ls = sub.add_parser("list-sessions", help="Wypisz dostępne sesje")
    p_ls.set_defaults(func=cmd_list_sessions)

    p_md = sub.add_parser("export-md", help="Eksport sesji do Markdown na stdout")
    p_md.add_argument("--session", help="Plik sesji (domyślna: latest)")
    p_md.set_defaults(func=cmd_export_md)

    args = ap.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
