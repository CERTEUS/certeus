#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/a11y_smoke.py                          |
# | ROLE: Project script.                                       |
# | PLIK: scripts/smokes/a11y_smoke.py                          |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""

PL: Prosty smoke test dostępności HTML (statyczne pliki w clients/web/*).
    Sprawdza minimalne kryteria: <html lang>, <meta viewport>, #main, skip-link
    oraz atrybuty alt na <img>.

EN: Simple accessibility smoke for static HTML pages (clients/web/*).
    Checks minimal criteria: <html lang>, <meta viewport>, #main, skip-link,
    and alt attributes for <img>.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import re

# === KONFIGURACJA / CONFIGURATION ===

ROOT = Path(__file__).resolve().parents[2]
PAGES = [
    ROOT / "clients/web/proof_visualizer/index.html",
    ROOT / "clients/web/mismatch_console/index.html",
    *(ROOT / "clients/web/public").glob("*.html"),
]


# === MODELE / MODELS ===


# === LOGIKA / LOGIC ===


def check_page(p: Path) -> list[str]:
    errs: list[str] = []
    text = p.read_text(encoding="utf-8", errors="ignore")

    if not re.search(r"<html[^>]*\blang=\"[a-zA-Z-]+\"", text):
        errs.append("missing <html lang>")

    if "<meta name=\"viewport\"" not in text:
        errs.append("missing <meta viewport>")

    if not re.search(r"id=\"main\"", text):
        errs.append("missing #main container")

    if not re.search(r"<a[^>]+href=\"#main\"", text):
        errs.append("missing skip-link to #main")

    for m in re.finditer(r"<img([^>]*)>", text, flags=re.IGNORECASE):
        attrs = m.group(1)
        if "alt=" not in attrs:
            errs.append("img without alt attribute")
            break

    return errs


def main() -> int:
    pages = [p for p in PAGES if p.exists()]
    all_errs: dict[str, list[str]] = {}
    for p in pages:
        errs = check_page(p)
        if errs:
            all_errs[str(p)] = errs

    if all_errs:
        print("A11y smoke failed:")
        for k, vs in all_errs.items():
            print(f" - {k}:")
            for e in vs:
                print(f"   * {e}")
        return 1

    print(f"A11y smoke passed on {len(pages)} pages")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
