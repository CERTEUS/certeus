#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/truth/test_jurisdiction_transform_property.py  |

# | ROLE: Project test.                                         |

# | PLIK: tests/truth/test_jurisdiction_transform_property.py  |

# | ROLA: Test projektu.                                        |

# +-------------------------------------------------------------+

"""
PL: Testy property‑based dla Ω‑Kernel – transformacja jurysdykcji (PL↔EU) i holonomia.

EN: Property‑based tests for Ω‑Kernel – jurisdiction transform (PL↔EU) and holonomy.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from hypothesis import given, strategies as st

from core.omega_jurisdiction import (
    holonomy_drift_jurisdiction,
    transform_jurisdiction,
)

# === KONFIGURACJA / CONFIGURATION ===

TOKENS_PL = [
    "ustawa",
    "rozporządzenie",
    "kodeks",
    "dowód",  # out‑of‑mapping token (should pass through)
]


def _sentence_pl(tokens: list[str]) -> str:
    return " ".join(tokens)


# === LOGIKA / LOGIC ===


@given(st.lists(st.sampled_from(TOKENS_PL), min_size=1, max_size=8))
def test_roundtrip_holonomy_zero_for_known_tokens(tokens: list[str]) -> None:
    """PL: Dla zdań złożonych z tokenów bazowych, drift holonomii wynosi 0.

    EN: For sentences from base tokens, holonomy drift equals 0.
    """

    text = _sentence_pl(tokens)
    unit = {"text": text, "jurisdiction": "pl"}
    drift = holonomy_drift_jurisdiction(unit, cycle=("pl", "eu"))
    assert drift == 0.0


@given(st.text(min_size=0, max_size=64))
def test_identity_when_target_equals_source(text: str) -> None:
    unit = {"text": text, "jurisdiction": "pl"}
    same = transform_jurisdiction(unit, "pl")
    assert same["jurisdiction"] == "pl"
    assert " ".join((same["text"] or "").split()) == " ".join(text.split())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
