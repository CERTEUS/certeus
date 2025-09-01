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


def fix_file(p: Path) -> bool:
    text = p.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines(keepends=True)
    n = len(lines)
    out: list[str] = []
    changed = False

    # Track first non-empty/non-comment to allow shebang only at very top
    seen_code_or_doc = False

    for i, line in enumerate(lines):
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

    if changed:
        p.write_text("".join(out), encoding="utf-8")
    return changed


def main() -> None:
    touched = 0
    for p in ROOT.rglob("*.py"):
        rel = "/" + str(p.relative_to(ROOT)).replace("\\", "/")
        if any(seg in rel for seg in SKIP_DIR_CONTAINS):
            continue
        if fix_file(p):
            touched += 1
            print(f"[FIXED] {rel.lstrip('/')}")
    print(f"Done. Files fixed: {touched}")


if __name__ == "__main__":
    main()

