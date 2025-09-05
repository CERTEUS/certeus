#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/a11y_smoke.py                         |
# | ROLE: Smoke: public HTML A11y checks                         |
# | PLIK: scripts/smokes/a11y_smoke.py                         |
# | ROLA: Smoke: A11y sprawdzenie HTML public                    |
# +-------------------------------------------------------------+

"""
PL: Lekki smoke A11y: sprawdza pliki HTML w `clients/web/public/` pod kątem
    atrybutu `lang`, obecności `meta viewport` oraz landmarku `<main>`/`role="main"`
    lub linku skip‑to‑content.

EN: Lightweight A11y smoke: checks HTML files in `clients/web/public/` for
    `lang` attribute, `meta viewport` presence, and a `<main>`/`role="main"`
    landmark or a skip‑to‑content link.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import re

_RE_LANG = re.compile(r"<html[^>]*\slang=\"[a-zA-Z-]+\"", re.IGNORECASE)
_RE_VIEWPORT = re.compile(r"<meta[^>]*name=\"viewport\"", re.IGNORECASE)
_RE_MAIN = re.compile(r"<(main|[^>]*role=\"main\")[^>]*>", re.IGNORECASE)
_RE_SKIP = re.compile(r"<a[^>]*href=\"#main\"", re.IGNORECASE)

def check_public_html(root: str | Path | None = None) -> tuple[dict[str, list[str]], int]:
    """PL/EN: Zwraca (issues_by_file, checked_count). Nie rzuca wyjątków."""
    repo = Path(root or ".").resolve()
    web = repo / "clients" / "web" / "public"
    issues: dict[str, list[str]] = {}
    checked = 0
    if not web.exists():
        return issues, 0
    for p in sorted(web.glob("*.html")):
        try:
            html = p.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        errs: list[str] = []
        if not _RE_LANG.search(html):
            errs.append("missing <html lang=…>")
        if not _RE_VIEWPORT.search(html):
            errs.append("missing <meta name=\"viewport\">")
        if not (_RE_MAIN.search(html) or _RE_SKIP.search(html)):
            errs.append("missing <main>/role=main or skip link")
        if errs:
            issues[str(p)] = errs
        checked += 1
    return issues, checked

def main() -> int:  # pragma: no cover (integration)
    issues, checked = check_public_html()
    if checked == 0:
        print("A11y: no public HTML files found (clients/web/public)")
        return 0
    if issues:
        print("A11y: issues found:")
        for f, errs in issues.items():
            for e in errs:
                print(f" - {f}: {e}")
        # Report-only usage in CI; non-zero signals problems
        return 1
    print(f"A11y: OK ({checked} files)")
    return 0

# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
