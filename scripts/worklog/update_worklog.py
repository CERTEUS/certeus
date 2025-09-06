#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/worklog/update_worklog.py                   |
# | ROLE: Project script.                                       |
# | PLIK: scripts/worklog/update_worklog.py                   |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Aktualizuje WORKLOG.md o wpis (data/autor/gałąź/skrót zmian).
EN: Updates WORKLOG.md with an entry (date/author/branch/summary).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import os
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--summary", required=True, help="One-line summary")
    ap.add_argument("--details", help="Optional multi-line details")
    args = ap.parse_args()

    repo = Path(__file__).resolve().parents[2]
    p = repo / "WORKLOG.md"
    ts = datetime.now(UTC).strftime("%Y-%m-%d %H:%M:%SZ")
    actor = (
        os.getenv("GITHUB_ACTOR")
        or os.getenv("USER")
        or os.getenv("USERNAME")
        or "agent"
    )
    branch = (
        os.getenv("GITHUB_REF_NAME")
        or os.getenv("CI_BRANCH")
        or os.getenv("BRANCH")
        or "work/daily"
    )

    entry = [
        f"- {ts} [{actor}] ({branch}): {args.summary.strip()}",
    ]
    if args.details:
        for line in args.details.strip().splitlines():
            entry.append(f"  - {line}")

    if not p.exists():
        header = [
            "# CERTEUS — WORKLOG",
            "",
            "Zbiorczy dziennik prac — krótkie wpisy po każdej zmianie (gałąź, data, skrót).",
            "",
        ]
    else:
        header = []

    content = "\n".join(header + entry) + "\n"
    with p.open("a", encoding="utf-8") as f:
        f.write(content)
    print(f"Appended worklog entry to {p}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
