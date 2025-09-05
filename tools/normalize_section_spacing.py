# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tools/normalize_section_spacing.py                    |
# | ROLE: Normalize spacing around section markers in Python    |
# | PLIK: tools/normalize_section_spacing.py                    |
# | ROLA: Normalizuje odstępy wokół sekcji w plikach Python     |
# +-------------------------------------------------------------+

"""

PL: Narzędzie porządkujące puste linie w plikach .py.
    - Usuwa nadmiarowe puste linie.
    - Zapewnia po jednej pustej linii przed/po znacznikach sekcji
      (np. "# === IMPORTY / IMPORTS ===").
    - Nie zmienia logiki, nie przestawia importów.

EN: Utility to tidy up blank lines in .py files.
    - Collapses excessive blank lines.
    - Ensures single blank line around section markers
      (e.g. "# === IMPORTY / IMPORTS ===").
    - Does not alter logic or reorder imports.

Usage:
  python tools/normalize_section_spacing.py --write   # apply changes in-place
  python tools/normalize_section_spacing.py --check   # exit 1 if changes needed

Idempotent and safe to run multiple times.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path
import re
import subprocess
import sys

# === KONFIGURACJA / CONFIGURATION ===

SECTION_RE = re.compile(r"^#\s*===\s+.*?\s+===\s*$")

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def list_tracked_py_files(repo: Path) -> Iterable[Path]:
    try:
        # nosec B603: calls git with static args; not user-controlled
        out = subprocess.check_output(["git", "ls-files", "*.py"], cwd=str(repo))
        for line in out.decode("utf-8").splitlines():
            p = (repo / line).resolve()
            if p.is_file():
                yield p
    except Exception:  # nosec B112: fallback path is intentional and safe
        # Fallback: recurse, but skip common virtualenvs
        for p in repo.rglob("*.py"):
            if any(seg in {".venv", "venv", "env", "site-packages"} for seg in p.parts):
                continue
            yield p

def normalize_text(text: str) -> str:
    lines = text.splitlines()
    out: list[str] = []

    # Collapse consecutive blank lines to at most 1
    prev_blank = False
    for ln in lines:
        is_blank = ln.strip() == ""
        if is_blank and prev_blank:
            continue
        out.append(ln)
        prev_blank = is_blank

    # Ensure single blank line around section markers
    i = 0
    while i < len(out):
        if SECTION_RE.match(out[i].rstrip()):
            # ensure exactly one blank line before (unless at file start)
            if i > 0:
                # remove all previous blanks
                j = i - 1
                while j >= 0 and out[j].strip() == "":
                    out.pop(j)
                    i -= 1
                    j -= 1
                # insert one blank
                out.insert(i, "")
                i += 1
            # ensure exactly one blank line after (unless end of file)
            if i + 1 < len(out):
                # remove following blanks
                k = i + 1
                while k < len(out) and out[k].strip() == "":
                    out.pop(k)
                # insert one blank if next line is not EOF
                if i + 1 < len(out):
                    out.insert(i + 1, "")
                    i += 1
        i += 1

    # Strip leading/trailing blank lines
    while out and out[0].strip() == "":
        out.pop(0)
    while out and out[-1].strip() == "":
        out.pop()

    return "\n".join(out) + "\n"

def main(argv: list[str]) -> int:
    write = "--write" in argv
    check = "--check" in argv
    repo = Path(__file__).resolve().parents[1]
    changed = []
    for p in list_tracked_py_files(repo):
        try:
            original = p.read_text(encoding="utf-8")
        except Exception:
            continue
        normalized = normalize_text(original)
        if normalized != original:
            if write:
                p.write_text(normalized, encoding="utf-8")
            changed.append(str(p.relative_to(repo)))
    if check and changed:
        print("Files need normalization:")
        for f in changed:
            print(f" - {f}")
        return 1
    if write:
        print(f"Normalized {len(changed)} file(s)")
    return 0

if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
