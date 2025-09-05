#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/truth/test_lang_holonomy.py                    |

# | ROLE: Project test.                                         |

# | PLIK: tests/truth/test_lang_holonomy.py                    |

# | ROLA: Test projektu.                                        |

# +-------------------------------------------------------------+

"""
PL: Testy Ω-Kernel – transformacja `lang` i holonomia językowa.

EN: Ω-Kernel tests – `lang` transform and language holonomy.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from core.omega_lang import holonomy_drift, transform_lang

# === KONFIGURACJA / CONFIGURATION ===


def test_transform_pl_en_roundtrip_zero_drift():
    unit = {"text": "Publikuj dowód w sprawie", "lang": "pl"}
    drift = holonomy_drift(unit, cycle=("pl", "en"))
    assert drift == 0.0


def test_transform_changes_lang_and_tokens_basic():
    unit = {"text": "Analizuj dowód", "lang": "pl"}
    en = transform_lang(unit, "en")
    assert en["lang"] == "en"
    assert "analyze" in en["text"].lower()
    pl = transform_lang(en, "pl")
    assert pl["lang"] == "pl"
    assert "analizuj" in pl["text"].lower()


# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
