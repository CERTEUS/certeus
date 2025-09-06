#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/omega/test_jurisdiction_map_property.py       |
# | ROLE: Test module.                                          |
# | PLIK: tests/omega/test_jurisdiction_map_property.py       |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Property-based dla jurisdiction_map — idempotencja i stała liczba tokenów.
EN: Property-based for jurisdiction_map — idempotence and stable token count.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from hypothesis import given, settings, strategies as st

from core.omega.transforms import apply_transform, compute_gauge_drift

JUR_WORDS = [
    "ustawa",
    "USTAWA",
    "Ustawa",
    "rozporządzenie",
    "Rozporządzenie",
    "ROZPORZĄDZENIE",
    "kodeks",
    "Kodeks",
    "KODEKS",
]


_NOISE = st.text(
    alphabet=st.characters(blacklist_categories=("Cs", "Zs")), min_size=3, max_size=8
)


@settings(max_examples=25, deadline=None)
@given(
    st.lists(st.sampled_from(JUR_WORDS), min_size=3, max_size=10),
    st.lists(_NOISE, min_size=1, max_size=5),
)
def test_jurisdiction_map_idempotent_and_count_stable(
    words: list[str], noise: list[str]
) -> None:
    src = " ".join(words + noise)
    once, _ = apply_transform(src, "jurisdiction_map")
    twice, _ = apply_transform(once, "jurisdiction_map")
    assert once == twice
    d = compute_gauge_drift(src, once)
    assert d.token_count_delta == 0
