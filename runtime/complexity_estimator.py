# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: runtime/complexity_estimator.py                               |
# | ROLE:                                                               |
# |  PL: Szacunek złożoności → klasy HEAT (HOT/WARM/COLD).              |
# |  EN: Complexity estimation → HEAT classes (HOT/WARM/COLD).          |
# +=====================================================================+

"""PL: Prosty heurystyczny estymator HEAT. EN: Simple heuristic HEAT estimator."""

from __future__ import annotations

from typing import Literal

Heat = Literal["HOT", "WARM", "COLD"]


def estimate_heat(ctx: dict[str, object]) -> Heat:
    """PL: Wyznacz klasę HEAT. EN: Derive HEAT class."""
    # === IMPORTY / IMPORTS ===
    # === KONFIGURACJA / CONFIGURATION ===
    # === MODELE / MODELS ===
    # === LOGIKA / LOGIC ===
    # === I/O / ENDPOINTS ===
    # === TESTY / TESTS ===

    score = float(ctx.get("complexity_score", 0.5) or 0.5)
    if score < 0.3:
        return "HOT"
    if score < 0.7:
        return "WARM"
    return "COLD"
