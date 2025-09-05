#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_domain_map.py                      |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_domain_map.py                      |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy transformacji domenowych Ω‑Kernel (MED/SEC/CODE) — inwarianty Gauge.

EN: Tests for Ω‑Kernel domain transforms (MED/SEC/CODE) — Gauge invariants.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from core.omega.transforms import apply_transform, compute_gauge_drift


def _assert_bounded(base: str, out: str, *, j_max: float = 0.25, d_max: int = 2) -> None:
    d = compute_gauge_drift(base, out)
    assert d.jaccard_drift <= j_max
    assert d.token_count_delta <= d_max


def test_domain_map_med_bounded_drift() -> None:
    before = "Pacjent otrzymał lek, dawka zależna od choroba i objaw."
    after, _ = apply_transform(before, "domain_map", domain="med")
    assert after != before
    _assert_bounded(before, after, j_max=0.30, d_max=2)


def test_domain_map_sec_bounded_drift() -> None:
    before = "Poważność podatność z CVE i wektor atak wg CVSS."
    after, _ = apply_transform(before, "domain_map", domain="sec")
    assert after != before
    _assert_bounded(before, after, j_max=0.30, d_max=2)


def test_domain_map_code_bounded_drift() -> None:
    before = "Funkcja w moduł rzuca wyjątek; błąd w imporcie i test."
    after, _ = apply_transform(before, "domain_map", domain="code")
    assert after != before
    _assert_bounded(before, after, j_max=0.30, d_max=2)


# === TESTY / TESTS ===
