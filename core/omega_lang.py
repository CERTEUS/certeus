#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/omega_lang.py                                   |

# | ROLE: Project module.                                       |

# | PLIK: core/omega_lang.py                                    |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Ω-Kernel – transformacja językowa (PL/EN) z pomiarem holonomii.

EN: Ω-Kernel – language transform (PL/EN) with holonomy measurement.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

_PL2EN: dict[str, str] = {
    "dowód": "proof",
    "publikuj": "publish",
    "sprawa": "case",
    "analizuj": "analyze",
    "odśwież": "refresh",
    "podgląd": "preview",
}

_EN2PL: dict[str, str] = {v: k for k, v in _PL2EN.items()}


# === MODELE / MODELS ===


@dataclass(slots=True)
class TextUnit:
    """Normalized text unit with language tag.

    PL: Reprezentuje tekst z metadanymi języka.
    EN: Represents a text with language metadata.
    """

    text: str
    lang: str  # "pl" | "en"

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any] | str) -> TextUnit:
        if isinstance(obj, str):
            return cls(text=obj, lang="pl")
        return cls(
            text=str(obj.get("text") or ""), lang=str(obj.get("lang") or "pl").lower()
        )

    def to_obj(self) -> dict[str, Any]:
        return {"text": self.text, "lang": self.lang}


# === LOGIKA / LOGIC ===


def _map_tokens(s: str, mapping: Mapping[str, str]) -> str:
    # Very small, token-wise reversible dictionary mapping; case-insensitive, preserves case for ASCII.
    out: list[str] = []
    for raw in s.split():
        low = raw.lower()
        if low in mapping:
            mapped = mapping[low]
            # Preserve capitalization of first letter if present
            if raw and raw[0].isupper():
                mapped = mapped.capitalize()
            out.append(mapped)
        else:
            out.append(raw)
    return " ".join(out)


def transform_lang(obj: Mapping[str, Any] | str, target_lang: str) -> dict[str, Any]:
    """
    PL: Przetłumacz prosty tekst (tokenowo) między PL↔EN, ustawiając `lang`.

    EN: Translate a simple text (token-wise) between PL↔EN, setting `lang`.
    """

    unit = TextUnit.from_obj(obj)
    tgt = (target_lang or "pl").lower()
    if unit.lang == tgt:
        return unit.to_obj()
    if unit.lang.startswith("pl") and tgt.startswith("en"):
        return TextUnit(text=_map_tokens(unit.text, _PL2EN), lang="en").to_obj()
    if unit.lang.startswith("en") and tgt.startswith("pl"):
        return TextUnit(text=_map_tokens(unit.text, _EN2PL), lang="pl").to_obj()
    # Unknown pair – return as-is with normalized tag
    unit.lang = tgt
    return unit.to_obj()


def holonomy_drift(
    obj: Mapping[str, Any] | str, *, cycle: tuple[str, str] = ("pl", "en")
) -> float:
    """
    PL: Zmierz drift holonomii po cyklu transformacji językowej, np. pl→en→pl.

    EN: Measure holonomy drift after a language transform cycle, e.g., pl→en→pl.
    """

    unit0 = TextUnit.from_obj(obj)
    a, b = cycle
    t1 = transform_lang(unit0.to_obj(), a)
    t2 = transform_lang(t1, b)
    t3 = transform_lang(t2, a)
    # Simple drift metric: 0.0 if texts equal ignoring case/extra spaces; else 1.0 (MVP)
    norm0 = " ".join(unit0.text.lower().split())
    norm3 = " ".join(str(t3.get("text") or "").lower().split())
    return 0.0 if norm0 == norm3 else 1.0


__all__ = ["transform_lang", "holonomy_drift", "TextUnit"]

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
