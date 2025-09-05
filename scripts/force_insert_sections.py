#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/force_insert_sections.py                    |
# | ROLE: Project module.                                       |
# | PLIK: scripts/force_insert_sections.py                    |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Wymusza wstawienie znaczników sekcji (21.1) do plików Python bez nich.
EN: Force-inserts Section 21.1 markers into Python files that miss them.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SKIP_DIR_CONTAINS = (
    "/.git/",
    "/.venv/",
    "/node_modules/",
    "/__pycache__/",
    "/.ruff_cache/",
    "/.pytest_cache/",
    "/dist/",
    "/build/",
)

MARKERS = (
    "# === IMPORTY / IMPORTS ===\n"
    "# === KONFIGURACJA / CONFIGURATION ===\n"
    "# === MODELE / MODELS ===\n"
    "# === LOGIKA / LOGIC ===\n"
    "# === I/O / ENDPOINTS ===\n"
    "# === TESTY / TESTS ===\n\n"
)


def needs_markers(text: str) -> bool:
    head = "\n".join(text.splitlines()[:200])
    return "# === " not in head


def insert_after_docstring_or_banner(text: str) -> str:
    lines = text.splitlines(keepends=True)
    n = len(lines)
    i = 0
    # skip shebang
    if i < n and lines[i].startswith("#!"):
        i += 1
    # skip initial comments
    while i < n and (lines[i].lstrip().startswith("#") or lines[i].strip() == ""):
        i += 1
    # if next line starts docstring
    if i < n and (lines[i].lstrip().startswith('"""') or lines[i].lstrip().startswith("'''")):
        quote = lines[i].lstrip()[:3]
        # move to end of docstring
        i += 1
        while i < n and quote not in lines[i]:
            i += 1
        if i < n:
            i += 1  # include closing line
    insert_at = i
    return "".join(lines[:insert_at] + [MARKERS] + lines[insert_at:])


def main() -> None:
    updated = 0
    for p in ROOT.rglob("*.py"):
        rel = "/" + str(p.relative_to(ROOT)).replace("\\", "/")
        if any(seg in rel for seg in SKIP_DIR_CONTAINS):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        if not needs_markers(text):
            continue
        new_text = insert_after_docstring_or_banner(text)
        if new_text != text:
            p.write_text(new_text, encoding="utf-8")
            updated += 1
            print(f"[FORCE-SECTIONS] {rel.lstrip('/')}")
    print(f"Done. Force sections updated: {updated}")


if __name__ == "__main__":
    main()
