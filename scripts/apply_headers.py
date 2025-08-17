# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/scripts/apply_headers.py                |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/apply_headers.py                              |
# | ROLE: Auto-add CERTEUS header block and module docstrings   |
# |       to Python files that are missing them.                |
# | PLIK: scripts/apply_headers.py                              |
# | ROLA: Automatyczne dodanie nagłówków i docstringów modułów  |
# |       do plików Python bez tych elementów.                  |
# +-------------------------------------------------------------+
"""
PL: Skrypt skanuje repozytorium, znajduje pliki .py i dodaje:
    (1) standardowy nagłówek CERTEUS (ASCII box) oraz
    (2) module docstring PL/EN — jeśli brakuje.
    Działa idempotentnie (nie dubluje nagłówków).
EN: The script scans the repo for .py files and adds:
    (1) a standard CERTEUS header block (ASCII box), and
    (2) a PL/EN module docstring — if missing.
    Idempotent (won't duplicate headers).
"""

from __future__ import annotations

import ast
import os
from pathlib import Path
from typing import Iterable


# === KONFIG: które katalogi skanować ========================== #
SCAN_DIRS = [
    "cje",
    "clients",
    "core",
    "kernel",
    "plugins",
    "scripts",
    "services",
    "tests",
]

# Pliki, które zwykle pomijamy (jeśli chcesz – usuń z listy)
SKIP_FILES = {
    "plugins/__init__.py",  # często pusty
}


# === Generator nagłówka ======================================= #
def build_header(rel_path: str) -> str:
    """
    Zwraca standardowy nagłówek CERTEUS z dynamiczną ścieżką pliku.
    """
    box = (
        "# +-------------------------------------------------------------+\n"
        "# |                          CERTEUS                            |\n"
        "# +-------------------------------------------------------------+\n"
        f"# | FILE: {rel_path:<52}|\n"
        "# | ROLE: Project module.                                       |\n"
        f"# | PLIK: {rel_path:<52}|\n"
        "# | ROLA: Moduł projektu.                                       |\n"
        "# +-------------------------------------------------------------+\n"
    )
    return box


# === Domyślny module docstring ================================ #
DEFAULT_DOCSTRING = (
    '"""\n'
    "PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.\n"
    "EN: CERTEUS module – please complete the functional description.\n"
    '"""\n'
)


# === Wykrywanie istniejącego nagłówka/docstringa ============== #
def has_header(text: str) -> bool:
    # szukamy znaku rozpoznawczego w pierwszych ~10 liniach
    head = "\n".join(text.splitlines()[:10])
    return "CERTEUS" in head and "FILE:" in head


def has_module_docstring(text: str) -> bool:
    try:
        tree = ast.parse(text)
        return ast.get_docstring(tree) is not None
    except Exception:
        # Jeśli nie możemy sparsować (np. niekompletna składnia), uznaj brak
        return False


# === Wstawianie nagłówka/docstringa =========================== #
def ensure_header_and_docstring(path: Path, project_root: Path) -> bool:
    """
    Modyfikuje plik, jeśli brakuje nagłówka lub docstringa.
    Zwraca True, jeśli plik został zmodyfikowany.
    """
    text = path.read_text(encoding="utf-8", errors="ignore")
    changed = False

    # zachowaj shebang/encoding (jeśli są w 1. linii)
    lines = text.splitlines(keepends=True)
    shebang = ""
    if lines and lines[0].startswith("#!"):
        shebang = lines[0]
        body = "".join(lines[1:])
    else:
        body = text

    # 1) Nagłówek
    if not has_header(body):
        rel = str(path.relative_to(project_root)).replace("\\", "/")
        header = build_header(rel)
        body = header + ("\n" if not body.startswith("\n") else "") + body
        changed = True

    # 2) Module docstring
    if not has_module_docstring(body):
        # Docstring musi być pierwszym statementem modułu → wstawiamy na samą górę body
        body = DEFAULT_DOCSTRING + ("\n" if not body.startswith("\n") else "") + body
        changed = True

    if changed:
        new_text = (shebang + body) if shebang else body
        # Na Windows trzymajmy CRLF (Git i tak poradzi sobie z autocrlf)
        new_text = new_text.replace("\r\n", "\n").replace("\n", os.linesep)
        path.write_text(new_text, encoding="utf-8")
    return changed


# === Skan repo i przetwarzanie ================================ #
def iter_python_files(root: Path, dirs: Iterable[str]) -> Iterable[Path]:
    for d in dirs:
        p = root / d
        if not p.exists():
            continue
        for py in p.rglob("*.py"):
            rel = str(py.relative_to(root)).replace("\\", "/")
            if rel in SKIP_FILES:
                continue
            yield py


def main() -> None:
    root = Path(__file__).resolve().parents[1]  # repo root
    changed_total = 0
    for py in iter_python_files(root, SCAN_DIRS):
        if ensure_header_and_docstring(py, root):
            changed_total += 1
            print(f"[UPDATED] {py.relative_to(root)}")
    print(f"\nDone. Files updated: {changed_total}")


if __name__ == "__main__":
    main()
