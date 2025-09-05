#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/omega_jurisdiction.py                           |

# | ROLE: Project module.                                       |

# | PLIK: core/omega_jurisdiction.py                            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Ω‑Kernel — transformacja jurysdykcji (PL↔EU) i pomiar holonomii.

EN: Ω‑Kernel — jurisdiction transform (PL↔EU) with holonomy measurement.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

_PL2EU: dict[str, str] = {
    # Minimal, token-wise legal terminology mapping (illustrative)
    "ustawa": "act",
    "rozporządzenie": "regulation",
    "kodeks": "code",
}

_EU2PL: dict[str, str] = {v: k for k, v in _PL2EU.items()}


# === MODELE / MODELS ===


@dataclass(slots=True)
class JurText:
    """Text with jurisdiction metadata.

    PL: Tekst z metadanymi jurysdykcji (np. PL/EU).
    EN: Text with jurisdiction metadata (e.g., PL/EU).
    """

    text: str
    jurisdiction: str  # "pl" | "eu"

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any] | str, default_jur: str = "pl") -> JurText:
        if isinstance(obj, str):
            return cls(text=obj, jurisdiction=default_jur)
        return cls(
            text=str(obj.get("text") or ""),
            jurisdiction=str(obj.get("jurisdiction") or default_jur).lower(),
        )

    def to_obj(self) -> dict[str, Any]:
        return {"text": self.text, "jurisdiction": self.jurisdiction}


# === LOGIKA / LOGIC ===


def _map_tokens(s: str, mapping: Mapping[str, str]) -> str:
    """Case-insensitive token mapping that preserves first-letter capitalization."""
    out: list[str] = []
    for raw in s.split():
        low = raw.lower()
        if low in mapping:
            mapped = mapping[low]
            if raw and raw[0].isupper():
                mapped = mapped.capitalize()
            out.append(mapped)
        else:
            out.append(raw)
    return " ".join(out)


def transform_jurisdiction(obj: Mapping[str, Any] | str, target: str) -> dict[str, Any]:
    """
    PL: Przekształć tekst między profilami jurysdykcji (PL↔EU), ustawiając pole `jurisdiction`.

    EN: Transform text between jurisdiction profiles (PL↔EU), setting the `jurisdiction` field.
    """

    unit = JurText.from_obj(obj)
    tgt = (target or "pl").lower()
    if unit.jurisdiction == tgt:
        return unit.to_obj()
    if unit.jurisdiction.startswith("pl") and tgt.startswith("eu"):
        return JurText(text=_map_tokens(unit.text, _PL2EU), jurisdiction="eu").to_obj()
    if unit.jurisdiction.startswith("eu") and tgt.startswith("pl"):
        return JurText(text=_map_tokens(unit.text, _EU2PL), jurisdiction="pl").to_obj()
    unit.jurisdiction = tgt
    return unit.to_obj()


def holonomy_drift_jurisdiction(
    obj: Mapping[str, Any] | str,
    *,
    cycle: tuple[str, str] = ("pl", "eu"),
) -> float:
    """
    PL: Zmierz drift holonomii po cyklu jurysdykcji, np. PL→EU→PL.

    EN: Measure holonomy drift after a jurisdiction transform cycle, e.g., PL→EU→PL.
    """

    unit0 = JurText.from_obj(obj)
    a, b = cycle
    t1 = transform_jurisdiction(unit0.to_obj(), a)
    t2 = transform_jurisdiction(t1, b)
    t3 = transform_jurisdiction(t2, a)
    norm0 = " ".join(unit0.text.lower().split())
    norm3 = " ".join(str(t3.get("text") or "").lower().split())
    return 0.0 if norm0 == norm3 else 1.0


__all__ = [
    "JurText",
    "transform_jurisdiction",
    "holonomy_drift_jurisdiction",
]


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
