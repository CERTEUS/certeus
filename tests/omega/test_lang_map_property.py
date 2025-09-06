#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_lang_map_property.py               |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_lang_map_property.py               |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Property-based dla lang_map (PL→EN→PL) — holonomia niskodryfowa.
EN: Property-based for lang_map (PL→EN→PL) — low-drift holonomy.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from hypothesis import given, settings, strategies as st

from core.omega.transforms import apply_transform, compute_gauge_drift

PL_LEX = [
    "ustawa",
    "Ustawa",
    "USTAWA",
    "rozporządzenie",
    "Rozporządzenie",
    "kodeks",
    "Kodeks",
]


@settings(max_examples=25, deadline=None)
@given(st.lists(st.sampled_from(PL_LEX), min_size=3, max_size=10))
def test_lang_map_cycle_low_drift(pl_words: list[str]) -> None:
    src = " ".join(pl_words)
    en_txt, _ = apply_transform(src, "lang_map", src="pl", dst="en")
    back, _ = apply_transform(en_txt, "lang_map", src="en", dst="pl")
    d = compute_gauge_drift(src, back)
    assert d.jaccard_drift <= 0.15
    assert d.token_count_delta <= 2
