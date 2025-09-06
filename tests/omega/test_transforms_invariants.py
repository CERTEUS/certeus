#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_transforms_invariants.py           |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_transforms_invariants.py           |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy inwariantów Gauge dla transformacji Ω‑Kernel.

EN: Gauge invariants tests for Ω‑Kernel transformations.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from core.omega.transforms import apply_transform, compute_gauge_drift, normalize_text

# === TESTY / TESTS ===


def test_identity_no_drift() -> None:
    txt = "Ustawa z dnia 20 lipca 2018 r. — Prawo"
    out, drift = apply_transform(txt, "identity")
    assert out == txt
    assert drift.token_count_delta == 0
    assert drift.jaccard_drift == 0.0


def test_normalize_low_drift() -> None:
    txt = "“Ustawa” z dnia 20 lipca 2018 r. – Prawo"
    out = normalize_text(txt, lang="pl")
    drift = compute_gauge_drift(txt, out)
    # Normalizacja nie zmienia znacząco zbioru tokenów
    assert drift.jaccard_drift <= 0.05
    assert drift.token_count_delta <= 1


def test_jurisdiction_map_drift_bounded() -> None:
    txt = "Ta ustawa i rozporządzenie oraz Kodeks cywilny."
    out, drift = apply_transform(txt, "jurisdiction_map")
    # Podmiany terminów nie mogą powodować skrajnego dryfu (MVP: ≤0.7)
    assert 0.0 <= drift.jaccard_drift <= 0.7
    assert out != txt
