"""
Dodaje standardowe znaczniki sekcji (sekcja 21.1) do krytycznych modułów
Python: core/pco/** i services/api_gateway/**, jeśli jeszcze ich nie ma.

Wstawiane nagłówki (po docstringu modułu):
- # === IMPORTY / IMPORTS ===
- # === KONFIGURACJA / CONFIGURATION ===
- # === MODELE / MODELS ===
- # === LOGIKA / LOGIC ===
- # === I/O / ENDPOINTS ===

EN: Inserts section markers after module docstring to make file structure
consistent with Section 21.1. Idempotent.
"""

from __future__ import annotations

import ast
from pathlib import Path

TARGET_DIRS = [
    "architectus",
    "cje",
    "clients",
    "core",
    "kernel",
    "plugins",
    "policies",
    "security",
    "services",
    "scripts",
    "tests",
]

MARKERS = [
    "# === IMPORTY / IMPORTS ===\n",
    "# === KONFIGURACJA / CONFIGURATION ===\n",
    "# === MODELE / MODELS ===\n",
    "# === LOGIKA / LOGIC ===\n",
    "# === I/O / ENDPOINTS ===\n",
    "# === TESTY / TESTS ===\n",
]


def has_any_marker(text: str) -> bool:
    head = "\n".join(text.splitlines()[:120])
    return "# === " in head


def find_docstring_span(text: str) -> tuple[int, int] | None:
    try:
        mod = ast.parse(text)
    except Exception:
        return None
    if not mod.body:
        return None
    node = mod.body[0]
    if (
        isinstance(node, ast.Expr)
        and isinstance(getattr(node, "value", None), ast.Constant)
        and isinstance(node.value.value, str)
    ):
        start = node.lineno - 1
        end = getattr(node, "end_lineno", node.lineno) - 1
        return (start, end)
    return None


def ensure_markers(text: str, rel: str) -> str | None:
    if has_any_marker(text):
        return None
    span = find_docstring_span(text)
    if not span:
        return None
    start, end = span
    lines = text.splitlines(keepends=True)
    insert_at = end + 1
    block = []
    # Ensure one blank line before markers
    if insert_at < len(lines) and lines[insert_at].strip() != "":
        block.append("\n")
    block.extend(MARKERS)
    block.append("\n")
    new_lines = lines[:insert_at] + block + lines[insert_at:]
    return "".join(new_lines)


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    updated = 0
    for td in TARGET_DIRS:
        base = root / td
        if not base.exists():
            continue
        for f in base.rglob("*.py"):
            text = f.read_text(encoding="utf-8", errors="ignore")
            new_text = ensure_markers(text, str(f.relative_to(root)))
            if new_text and new_text != text:
                f.write_text(new_text, encoding="utf-8")
                updated += 1
                print(f"[SECTIONS] {f.relative_to(root)}")
    print(f"Done. Files updated: {updated}")


if __name__ == "__main__":
    main()
