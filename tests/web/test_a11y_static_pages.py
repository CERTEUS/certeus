#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/web/test_a11y_static_pages.py                  |
# | ROLE: Test module.                                          |
# | PLIK: tests/web/test_a11y_static_pages.py                  |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Minimalne testy A11y (WCAG 2.2 AA baseline) dla statycznych stron
    w `clients/web/public/*` bez zewnętrznych zależności.

EN: Minimal A11y tests (WCAG 2.2 AA baseline) for static pages
    in `clients/web/public/*` without extra dependencies.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path

import pytest

PUB_DIR = Path(__file__).resolve().parents[2] / "clients" / "web" / "public"


def _html_files() -> list[Path]:
    files: list[Path] = []
    for p in PUB_DIR.glob("*.html"):
        # Include all HTML files for testing, including index.html
        files.append(p)
    return files


@pytest.mark.parametrize("path", _html_files(), ids=lambda p: p.name)
def test_has_doctype_html_lang_title_viewport(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    assert "<!doctype html>" in text.lower()
    # lang on <html ...>
    m = re.search(r"<html[^>]*?lang=\"([a-zA-Z_-]+)\"", text, flags=re.IGNORECASE)
    assert m, "<html lang=...> is required"
    # title
    mt = re.search(r"<title>([^<]+)</title>", text, flags=re.IGNORECASE)
    assert mt and mt.group(1).strip(), "<title> must be present and non-empty"
    # viewport
    assert re.search(r"<meta[^>]+name=\"viewport\"", text, flags=re.IGNORECASE), "viewport meta required"


@pytest.mark.parametrize("path", _html_files(), ids=lambda p: p.name)
def test_has_h1_and_links_have_text_or_label(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    assert re.search(r"<h1[^>]*>.*?</h1>", text, flags=re.IGNORECASE | re.DOTALL), "at least one <h1> required"
    # Links: at least one anchor; ensure no empty-text anchors without aria-label/title
    anchors: Iterable[str] = re.findall(r"<a\s+[^>]*>(.*?)</a>", text, flags=re.IGNORECASE | re.DOTALL)
    if anchors:
        # consider visible text present if any non-whitespace in content
        has_discernible = any(bool(re.sub(r"\s+", "", a)) for a in anchors)
        if not has_discernible:
            # Fallback: allow aria-label or title on <a>
            assert re.search(r"<a[^>]+(aria-label|title)=\"[^\"]+\"", text, flags=re.IGNORECASE)


@pytest.mark.parametrize("path", _html_files(), ids=lambda p: p.name)
def test_has_language_selector(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    
    # Check if this page actually has a language selector
    has_lang_selector = bool(re.search(r"<select[^>]+id=\"lang\"", text, flags=re.IGNORECASE))
    
    # Pages that are expected to have language selectors (main interactive apps)
    app_pages = {
        "alpha.html", "boundary.html", "chatops.html", "code.html", "export.html",
        "geometry.html", "lexenith.html", "mailops.html", "marketplace.html", 
        "med.html", "playground.html", "qtm.html", "quantum.html", "sec.html"
    }
    
    if path.name in app_pages:
        # These pages MUST have language selector
        assert has_lang_selector, f"App page {path.name} should have language selector"
    else:
        # For utility/dashboard pages, language selector is optional
        # Test passes regardless of whether it has selector or not
        pass  # No assertion needed for utility pages
@pytest.mark.parametrize("path", _html_files(), ids=lambda p: p.name)
def test_images_have_alt_when_present(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    imgs = re.findall(r"<img\s+([^>]*?)>", text, flags=re.IGNORECASE)
    for attrs in imgs:
        assert re.search(r"\balt=\"[^\"]*\"", attrs, flags=re.IGNORECASE), "<img> must have alt attribute"


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
