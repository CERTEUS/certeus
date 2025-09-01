#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/fix_decorator_split.py                      |
# | ROLE: Project module.                                       |
# | PLIK: scripts/fix_decorator_split.py                      |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Naprawia przypadki, gdzie znacznik sekcji (# === ... ===) wstawiono między
dekorator a docelową definicję (class/def). Usuwa też zbłąkane shebangi
pojawiające się w środku plików.

EN: Fix cases where a section marker was inserted between a decorator and its
target (class/def). Also removes stray mid-file shebang lines.

--check mode: report-only (exit 0), no modifications.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import argparse

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


def fix_file(p: Path, *, check_only: bool = False) -> bool:
    text = p.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    changed = False

    # (we only ensure no mid-file shebangs; top-only allowed)

    for _i, line in enumerate(lines):
        stripped = line.lstrip()
        # Remove mid-file shebangs
        if stripped.startswith("#!/usr/bin/env python3"):
            if out:  # not at very top
                changed = True
                continue
        # Remove section marker immediately following a decorator block
        if stripped.startswith("# === "):
            # Look back for previous significant line in out
            k = len(out) - 1
            while k >= 0 and (out[k].strip() == "" or out[k].lstrip().startswith("#")):
                k -= 1
            prev = out[k].lstrip() if k >= 0 else ""
            if prev.startswith("@"):
                changed = True
                continue
        out.append(line)

    if changed and not check_only:
        p.write_text("".join(out), encoding="utf-8")
    return changed


def main() -> None:
    parser = argparse.ArgumentParser(description="Fix decorator splits and stray shebangs")
    parser.add_argument("--check", action="store_true", help="Report-only; do not modify files")
    args = parser.parse_args()

    touched = 0
    reported = 0
    for p in ROOT.rglob("*.py"):
        rel = "/" + str(p.relative_to(ROOT)).replace("\\", "/")
        if any(seg in rel for seg in SKIP_DIR_CONTAINS):
            continue
        if fix_file(p, check_only=args.check):
            if args.check:
                print(f"[WOULD-FIX] {rel.lstrip('/')}")
                reported += 1
            else:
                touched += 1
                print(f"[FIXED] {rel.lstrip('/')}")
    if args.check:
        print(f"Done. Would fix: {reported}")
    else:
        print(f"Done. Files fixed: {touched}")


if __name__ == "__main__":
    main()
