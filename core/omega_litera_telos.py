#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/omega_litera_telos.py                           |

# | ROLE: Project module.                                       |

# | PLIK: core/omega_litera_telos.py                            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Ω‑Kernel — transformacja interpretacji litera↔telos (L/T) i pomiar holonomii.

EN: Ω‑Kernel — letter↔telos interpretation transform (L/T) with holonomy metric.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

# Minimalny, tokenowy słownik dla ilustracji koncepcji L/T.
_L2T: dict[str, str] = {
    "literalnie": "celowo",
    "przepis": "cel",
    "paragraf": "ratio",
    "zakaz": "ochrona",
    "wymóg": "intencja",
    "kara": "naprawa",
}

_T2L: dict[str, str] = {v: k for k, v in _L2T.items()}


# === MODELE / MODELS ===


@dataclass(slots=True)
class LTText:
    """Text with L/T interpretation tag.

    PL: Tekst z metadanymi interpretacji (litera/telos).
    EN: Text with interpretation metadata (letter/telos).
    """

    text: str
    lt: str  # "l" | "t"

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any] | str, default_mode: str = "l") -> LTText:
        if isinstance(obj, str):
            return cls(text=obj, lt=default_mode)
        return cls(
            text=str(obj.get("text") or ""),
            lt=str(obj.get("lt") or default_mode).lower(),
        )

    def to_obj(self) -> dict[str, Any]:
        return {"text": self.text, "lt": self.lt}


# === LOGIKA / LOGIC ===


def _map_tokens(s: str, mapping: Mapping[str, str]) -> str:
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


def transform_litera_telos(obj: Mapping[str, Any] | str, target: str) -> dict[str, Any]:
    """
    PL: Przekształcenie tokenowe między trybami interpretacji L↔T, ustawiając `lt`.

    EN: Token-wise transform between interpretation modes L↔T, setting `lt`.
    """

    unit = LTText.from_obj(obj)
    tgt = (target or "l").lower()
    if unit.lt == tgt:
        return unit.to_obj()
    if unit.lt.startswith("l") and tgt.startswith("t"):
        return LTText(text=_map_tokens(unit.text, _L2T), lt="t").to_obj()
    if unit.lt.startswith("t") and tgt.startswith("l"):
        return LTText(text=_map_tokens(unit.text, _T2L), lt="l").to_obj()
    unit.lt = tgt
    return unit.to_obj()


def holonomy_drift_lt(
    obj: Mapping[str, Any] | str, *, cycle: tuple[str, str] = ("l", "t")
) -> float:
    """
    PL: Zmierz drift po cyklu L→T→L (lub odwrotnie).

    EN: Measure drift after a L→T→L cycle (or reverse).
    """

    unit0 = LTText.from_obj(obj)
    a, b = cycle
    t1 = transform_litera_telos(unit0.to_obj(), a)
    t2 = transform_litera_telos(t1, b)
    t3 = transform_litera_telos(t2, a)
    norm0 = " ".join(unit0.text.lower().split())
    norm3 = " ".join(str(t3.get("text") or "").lower().split())
    return 0.0 if norm0 == norm3 else 1.0


__all__ = ["LTText", "transform_litera_telos", "holonomy_drift_lt"]


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
