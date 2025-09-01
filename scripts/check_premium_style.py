# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/check_premium_style.py                      |
# | ROLE: Project module.                                       |
# | PLIK: scripts/check_premium_style.py                      |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
CI Gate: Premium Code Style (sec. 21)

Sprawdza repo wg kluczowych punktów z sekcji 21:
- Python: baner CERTEUS + module docstring (PL/EN) + obecność sekcji (# === ... ===)
- YAML/HTML/JS/SH/PS1: nagłówek (baner) z FILE/PLIK i CERTEUS

Zwraca kod 0 (OK) lub 1 (naruszenia). Wypisuje listę problemów.
"""

from __future__ import annotations

import ast
from pathlib import Path
import sys

REPO = Path(__file__).resolve().parents[1]

SKIP_DIRS = {
    ".git",
    ".venv",
    "node_modules",
    "dist",
    "build",
    "__pycache__",
    ".ruff_cache",
    ".pytest_cache",
    "clients/web/public/brand",
}


def iter_files(patterns: list[str]) -> list[Path]:
    out: list[Path] = []
    for p in REPO.rglob("*"):
        if not p.is_file():
            continue
        rel = p.relative_to(REPO).as_posix()
        if any(rel.startswith(d + "/") or rel == d for d in SKIP_DIRS):
            continue
        if any(rel.endswith(suf) for suf in patterns):
            out.append(p)
    return out


def has_banner_head(text: str) -> bool:
    head = "\n".join(text.splitlines()[:15]).lower()
    return "certeus" in head and "file:" in head


def has_sections_head(text: str) -> bool:
    head = "\n".join(text.splitlines()[:200])
    return "# === " in head


def has_module_docstring(text: str) -> bool:
    try:
        tree = ast.parse(text)
    except Exception:
        return False
    return ast.get_docstring(tree) is not None


def check_python() -> list[str]:
    errs: list[str] = []
    for f in iter_files([".py"]):
        t = f.read_text(encoding="utf-8", errors="ignore")
        if not has_banner_head(t):
            errs.append(f"[PY][BANNER] {f.relative_to(REPO)}")
        if not has_module_docstring(t):
            errs.append(f"[PY][DOCSTRING] {f.relative_to(REPO)}")
        if not has_sections_head(t):
            errs.append(f"[PY][SECTIONS] {f.relative_to(REPO)}")
    return errs


def check_textual(exts: list[str], label: str) -> list[str]:
    errs: list[str] = []
    for f in iter_files(exts):
        t = f.read_text(encoding="utf-8", errors="ignore")
        if not has_banner_head(t):
            errs.append(f"[{label}][BANNER] {f.relative_to(REPO)}")
    return errs


def main() -> int:
    issues: list[str] = []
    issues += check_python()
    issues += check_textual([".yaml", ".yml"], "YAML")
    issues += check_textual([".html"], "HTML")
    issues += check_textual([".js"], "JS")
    issues += check_textual([".sh"], "SH")
    issues += check_textual([".ps1"], "PS1")

    if issues:
        print("Premium Code Style violations (sec.21):", file=sys.stderr)
        for line in issues:
            print(line, file=sys.stderr)
        return 1
    print("Premium Code Style: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
