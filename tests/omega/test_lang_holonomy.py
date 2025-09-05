#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_lang_holonomy.py                   |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_lang_holonomy.py                   |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Test holonomii językowej dla transformacji lang_map (PL↔EN) w Ω‑Kernel.
EN: Language holonomy test for lang_map (PL↔EN) in Ω‑Kernel.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from core.omega.transforms import apply_transform, compute_gauge_drift

# === TESTY / TESTS ===

def test_lang_map_pl_en_pl_holonomy_low_drift() -> None:
    src = "Ustawa i rozporządzenie oraz Kodeks cywilny."
    en_txt, _ = apply_transform(src, "lang_map", src="pl", dst="en")
    back, _ = apply_transform(en_txt, "lang_map", src="en", dst="pl")
    drift = compute_gauge_drift(src, back)
    assert drift.jaccard_drift <= 0.10
    assert drift.token_count_delta <= 2
