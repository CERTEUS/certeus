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
import threading
import time
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


def _read_records(session: Path) -> list[dict]:
    recs: list[dict] = []
    try:
        for line in session.read_text(encoding="utf-8").splitlines():
            s = line.strip()
            if not s:
                continue
            try:
                recs.append(json.loads(s))
            except Exception:
                # awaryjnie zapakuj jako tekst
                recs.append({"ts": _now_iso(), "role": "assistant", "text": s})
    except Exception:
        pass
    return recs


def _write_context_files(target: Path, items: list[dict]) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    payload = {"messages": items}
    target.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    # Markdown obok
    md = ["# Last messages (context)"]
    for it in items:
        ts = it.get("ts", "?")
        role = it.get("role", "?")
        text = it.get("text", "")
        md.append("")
        md.append(f"## {ts} • {role}")
        md.append("")
        md.append("```text")
        md.append(str(text))
        md.append("```")
    target.with_suffix(".md").write_text("\n".join(md) + "\n", encoding="utf-8")


def cmd_remember(args: argparse.Namespace) -> int:
    session = _resolve_session(args.session)
    recs = _read_records(session)
    k = int(max(1, args.count))
    last = recs[-k:] if recs else []
    out = Path(args.out) if args.out else _history_dir() / "context_last.json"
    _write_context_files(out, last)
    print(str(out))
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

    # tryb: daemon (zbiera wiadomości ze strumienia/pipe i scala w rekordy co ~1 min)
    p_da = sub.add_parser("daemon", help="Tryb autosave (czyta z pipe i zapisuje do sesji)")
    p_da.add_argument("--session", help="Plik sesji (domyślna: latest)")
    p_da.add_argument("--pipe", default=str(_history_dir() / "inbox.pipe"), help="Ścieżka do named pipe (FIFO)")
    p_da.add_argument("--idle-sec", type=int, default=60, help="Timeout łączenia chunków (sekundy)")
    p_da.set_defaults(func=cmd_daemon)

    # tryb: push (zapisz wiadomość do pipe; ułatwia integrację z Taskiem)
    p_push = sub.add_parser("push", help="Wyślij wiadomość do pipe (dla daemon)")
    p_push.add_argument("--pipe", default=str(_history_dir() / "inbox.pipe"), help="Ścieżka do named pipe (FIFO)")
    p_push.add_argument("--role", default="assistant", choices=["user", "assistant", "system"], help="Rola")
    p_push.add_argument("--text", required=True, help="Treść")
    p_push.set_defaults(func=cmd_push)

    p_mem = sub.add_parser("remember", help="Zapisz ostatnie N wiadomości do pliku kontekstu")
    p_mem.add_argument("--session", help="Plik sesji (domyślna: latest)")
    p_mem.add_argument("--count", type=int, default=5, help="Liczba wiadomości (domyślnie: 5)")
    p_mem.add_argument("--out", help="Ścieżka docelowa JSON (domyślnie: logs/codex_history/context_last.json)")
    p_mem.set_defaults(func=cmd_remember)

    args = ap.parse_args(argv)
    return int(args.func(args))


# === Implementacja trybu daemon/push ===


def _ensure_fifo(path: Path) -> None:
    try:
        if path.exists():
            return
        path.parent.mkdir(parents=True, exist_ok=True)
        os.mkfifo(path)
    except FileExistsError:
        pass


def cmd_push(args: argparse.Namespace) -> int:
    p = Path(args.pipe)
    _ensure_fifo(p)
    payload = json.dumps({"ts": _now_iso(), "role": args.role, "text": args.text}, ensure_ascii=False)
    # Otwórz FIFO i zapisz linię (blokuje, jeśli daemon nie czyta)
    with p.open("w", encoding="utf-8") as f:
        f.write(payload + "\n")
    return 0


def cmd_daemon(args: argparse.Namespace) -> int:
    session = _resolve_session(args.session)
    fifo = Path(args.pipe)
    _ensure_fifo(fifo)

    buf_role: str | None = None
    buf_text: list[str] = []
    last_at = 0.0
    idle = float(max(1, int(args.idle_sec)))
    stop = threading.Event()

    def _flush() -> None:
        nonlocal buf_role, buf_text, last_at
        if buf_role and buf_text:
            _append_message(session, buf_role, "\n".join(buf_text))
        buf_role = None
        buf_text = []
        last_at = 0.0

    def _ticker() -> None:
        while not stop.is_set():
            time.sleep(1.0)
            try:
                if buf_role and (time.time() - last_at) >= idle:
                    _flush()
            except Exception:
                pass

    th = threading.Thread(target=_ticker, daemon=True)
    th.start()

    print(f"[codex-history] daemon started → session={session.name} fifo={fifo}")
    try:
        with fifo.open("r", encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    role = str(obj.get("role") or "assistant")
                    text = str(obj.get("text") or "")
                except Exception:
                    role = "assistant"
                    text = line
                now = time.time()
                if (buf_role == role) and (now - last_at) < idle:
                    buf_text.append(text)
                    last_at = now
                else:
                    _flush()
                    buf_role = role
                    buf_text = [text]
                    last_at = now
    except KeyboardInterrupt:
        pass
    finally:
        stop.set()
        try:
            th.join(timeout=1.0)
        except Exception:
            pass
        _flush()
    print("[codex-history] daemon stopped")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
