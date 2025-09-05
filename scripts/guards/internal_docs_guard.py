#!/usr/bin/env python3
"""
CERTEUS — Internal Docs Guard

Fail PR if internal markers are present in public docs.

Rules:
- Scan text files under docs/** excluding docs/internal/** and docs/private/**.
- If a file contains markers like 'INTERNAL ONLY' or 'CONFIDENTIAL' (case-insensitive), fail.

Usage:
  python scripts/guards/internal_docs_guard.py
"""

from __future__ import annotations

from pathlib import Path
import sys

MARKERS = ("INTERNAL ONLY", "CONFIDENTIAL")


def is_text(p: Path) -> bool:
    try:
        b = p.read_bytes()
    except Exception:
        return False
    # Heuristic: allow ascii/utf-8 decodable
    try:
        b.decode("utf-8")
        return True
    except Exception:
        return False


def main() -> int:
    repo = Path(".").resolve()
    base = repo / "docs"
    if not base.exists():
        return 0
    offenders: list[Path] = []
    for p in base.rglob("*"):
        if not p.is_file():
            continue
        # exclude internal/private
        rel = p.relative_to(repo)
        if str(rel).startswith("docs/internal/") or str(rel).startswith("docs/private/"):
            continue
        if not is_text(p):
            continue
        try:
            txt = p.read_text(encoding="utf-8")
        except Exception:
            continue
        low = txt.lower()
        if any(m.lower() in low for m in MARKERS):
            offenders.append(rel)
    if offenders:
        sys.stderr.write("Internal-docs-guard: found internal markers in public docs:\n")
        for o in offenders:
            sys.stderr.write(f" - {o}\n")
        return 1
    print("Internal-docs-guard: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
