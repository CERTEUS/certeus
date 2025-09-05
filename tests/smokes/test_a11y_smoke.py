#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/smokes/test_a11y_smoke.py                       |
# | ROLE: Project test module.                                  |
# | PLIK: tests/smokes/test_a11y_smoke.py                       |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Test smoke A11y — funkcja analizy HTML zwraca strukturę wyników i
    co najmniej jeden plik został sprawdzony.

EN: A11y smoke test — the HTML analysis function returns results and
    at least one file was checked.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from scripts.smokes.a11y_smoke import check_public_html


def test_a11y_smoke_runs() -> None:
    issues, checked = check_public_html()
    assert isinstance(issues, dict)
    assert isinstance(checked, int)
    # Repository ships public pages; expect at least one checked file
    assert checked >= 1
