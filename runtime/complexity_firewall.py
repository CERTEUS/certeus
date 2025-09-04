#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: runtime/complexity_firewall.py                                 |
# | ROLE:                                                                |
# |  PL: Polityki SLA/priorytetów kolejek — parser wag (lekki stub).     |
# |  EN: SLA/queue priority policies — weights parser (light stub).      |
# +=====================================================================+

"""
PL: Udostępnia `parse_sla_weights()` — mapuje profile SLA na wagi kolejek.
EN: Exposes `parse_sla_weights()` — maps SLA profiles to queue weights.

Wagi mogą być nadpisane przez ENV `SLA_WEIGHTS` w formacie
"basic=1,gold=2,platinum=3". Błędy/parsy nie przerywają działania.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os


def parse_sla_weights() -> dict[str, int]:
    """Zwraca słownik wag SLA; bezpieczne domyślne wartości.

    Defaults: {"basic": 1, "gold": 2, "platinum": 3}.
    """

    default = {"basic": 1, "gold": 2, "platinum": 3}
    raw = (os.getenv("SLA_WEIGHTS") or "").strip()
    if not raw:
        return default
    out: dict[str, int] = {}
    try:
        for part in raw.split(","):
            if not part.strip():
                continue
            if "=" not in part:
                continue
            k, v = part.split("=", 1)
            k = k.strip().lower()
            try:
                out[k] = int(v.strip())
            except Exception:
                continue
        return out or default
    except Exception:
        return default


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
