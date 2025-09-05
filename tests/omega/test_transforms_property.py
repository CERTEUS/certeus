#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_transforms_property.py             |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_transforms_property.py             |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy property‑based (Hypothesis) dla Ω‑Kernel inwariantów.

EN: Property‑based (Hypothesis) tests for Ω‑Kernel invariants.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from hypothesis import given, settings, strategies as st

from core.omega.transforms import compute_gauge_drift, normalize_text


@settings(max_examples=25, deadline=None)
@given(
    st.lists(
        st.text(alphabet=st.characters(blacklist_categories=("Cs", "Zs")), min_size=1, max_size=8),
        min_size=3,
        max_size=10,
    )
)
def test_identity_is_stable(words: list[str]) -> None:
    txt = " ".join(words)
    d = compute_gauge_drift(txt, txt)
    assert d.jaccard_drift == 0.0 and d.token_count_delta == 0


_PUNCT = [",", ".", ";", ":", "-", "—", "–", "(", ")", "[", "]", '"', "'", "/"]


@settings(max_examples=25, deadline=None)
@given(
    st.lists(
        st.text(
            alphabet=st.characters(blacklist_categories=("Cs", "Zs")),
            min_size=1,
            max_size=8,
        ),
        min_size=3,
        max_size=10,
    ),
    st.lists(st.sampled_from(_PUNCT), min_size=2, max_size=6),
)
def test_normalize_limits_drift_under_punctuation_noise(words: list[str], punct: list[str]) -> None:
    base = " ".join(words)
    noisy = base
    for p in punct:
        noisy = p + noisy + p
    normalized = normalize_text(noisy)
    d = compute_gauge_drift(base, normalized)
    assert d.jaccard_drift <= 0.3
