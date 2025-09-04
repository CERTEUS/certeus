#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_transforms_entropy_entities.py      |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_transforms_entropy_entities.py      |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy dryfu entropii i NER‑like inwariantów dla Ω‑Kernel.

EN: Entropy and NER‑like invariant drift tests for Ω‑Kernel.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from core.omega.transforms import (
    apply_transform,
    compute_entity_drift,
    compute_entropy_drift,
    normalize_text,
)


def test_entropy_drift_small_for_normalize() -> None:
    txt = '“Ustawa” z dnia 20 lipca 2018 r. – Prawo'
    out, _ = apply_transform(txt, "normalize", lang="pl")
    ent = compute_entropy_drift(txt, out)
    assert ent.entropy_drift <= 0.2


def test_entity_drift_stable_on_punctuation_changes() -> None:
    before = 'Jan Kowalski 2020, Poznań — Polska.'
    after = normalize_text('Jan Kowalski 2020, Poznań – Polska.', lang="pl")
    drift = compute_entity_drift(before, after)
    # Heuristic extractor should see same entities → near zero drift
    assert drift.entity_jaccard_drift <= 0.1
