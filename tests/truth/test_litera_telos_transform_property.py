#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/truth/test_litera_telos_transform_property.py  |

# | ROLE: Project test.                                         |

# | PLIK: tests/truth/test_litera_telos_transform_property.py  |

# | ROLA: Test projektu.                                        |

# +-------------------------------------------------------------+

"""
PL: Testy property‑based – transformacje litera↔telos (L/T) i holonomia.

EN: Property‑based tests – letter↔telos (L/T) transforms and holonomy.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from hypothesis import given, strategies as st

from core.omega_litera_telos import holonomy_drift_lt, transform_litera_telos

# === KONFIGURACJA / CONFIGURATION ===

TOKENS_L = [
    "literalnie",
    "przepis",
    "paragraf",
    "zakaz",
    "wymóg",
    "kara",
]


def _sent(tokens: list[str]) -> str:
    return " ".join(tokens)


# === LOGIKA / LOGIC ===


@given(st.lists(st.sampled_from(TOKENS_L), min_size=1, max_size=8))
def test_roundtrip_zero_drift_for_known_tokens(tokens: list[str]) -> None:
    text = _sent(tokens)
    unit = {"text": text, "lt": "l"}
    drift = holonomy_drift_lt(unit, cycle=("l", "t"))
    assert drift == 0.0


@given(st.text(min_size=0, max_size=64))
def test_identity_if_target_equals_source(text: str) -> None:
    unit = {"text": text, "lt": "l"}
    same = transform_litera_telos(unit, "l")
    assert same["lt"] == "l"
    assert " ".join((same["text"] or "").split()) == " ".join(text.split())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
