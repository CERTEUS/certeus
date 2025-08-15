# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/check_headers.py                              |
# | ROLE: Pre-commit checker for CERTEUS header & module docstr |
# | PLIK: scripts/check_headers.py                              |
# | ROLA: Walidator nagłówka CERTEUS i docstringa modułu        |
# +-------------------------------------------------------------+
"""
PL: Skrypt uruchamiany przez pre-commit. Dla podanych plików .py
    sprawdza obecność nagłówka CERTEUS oraz module docstringa.
    Akceptuje kilka form nagłówka (baner z 'CERTEUS', lub linie
    zawierające 'FILE:'/'PLIK:'), żeby nie blokować developmentu.

EN: Pre-commit script. For given .py files, validates that a
    CERTEUS header and a module docstring are present. It accepts
    multiple header styles (banner with 'CERTEUS' or lines that
    contain 'FILE:'/'PLIK:') to avoid blocking development.
"""

from __future__ import annotations

# === stdlib imports (one-per-line for Ruff) ===================
import argparse
import ast
import sys
from pathlib import Path
from typing import Iterable, List


# ==============================================================
# == BLOCK: detection helpers                                  =
# ==============================================================


def _read_head(path: Path, head_lines: int = 30) -> str:
    """Read only the first N lines of the file for header detection."""
    try:
        lines: List[str] = []
        with path.open("r", encoding="utf-8", errors="ignore") as f:
            for i, line in enumerate(f):
                if i >= head_lines:
                    break
                lines.append(line)
        head: str = "".join(lines)
        return head
    except Exception:
        return ""


def _has_module_docstring(full_text: str) -> bool:
    """Parse AST and check for module docstring presence."""
    try:
        tree = ast.parse(full_text)
        return ast.get_docstring(tree) is not None
    except Exception:
        return False


def _has_certeus_header(head_text: str) -> bool:
    """
    Flexible header detection:
    - any line in head that contains 'CERTEUS' (banner or single line), OR
    - presence of 'FILE:' and/or 'PLIK:' markers, OR
    - SPDX license line if you decide to add one later.

    This matches the banner inserted by scripts/apply_headers.py.
    """
    head_lower: str = head_text.lower()
    if "certeus" in head_lower:
        return True
    if "file:" in head_lower or "plik:" in head_lower:
        return True
    if "spdx-license-identifier" in head_lower:
        return True
    return False


# ==============================================================
# == BLOCK: main check routine                                  =
# ==============================================================


def check_files(paths: Iterable[Path]) -> int:
    """
    Return exit code (0 ok, 1 failure). Prints issues as:
    [HEADER MISSING] <path>
    [DOCSTRING MISSING] <path>
    """
    missing: int = 0
    for p in paths:
        if p.suffix != ".py":
            continue
        if not p.exists():
            continue

        head: str = _read_head(p)
        try:
            full: str = p.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            full = head  # fallback

        # --- header
        if not _has_certeus_header(head):
            print(f"[HEADER MISSING] {p}")
            missing += 1

        # --- module docstring
        if not _has_module_docstring(full):
            print(f"[DOCSTRING MISSING] {p}")
            missing += 1

    return 0 if missing == 0 else 1


# ==============================================================
# == BLOCK: CLI entrypoint                                      =
# ==============================================================


def main() -> int:
    parser = argparse.ArgumentParser(
        description="CERTEUS header/docstring gate",
    )
    parser.add_argument("files", nargs="*", help="Files passed by pre-commit")
    args = parser.parse_args()

    paths = [Path(f) for f in args.files]
    return check_files(paths)


if __name__ == "__main__":
    sys.exit(main())
