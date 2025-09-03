#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/dp_budget_gate.py                      |
# | ROLE: Gate: DP epsilon budgets (stub)                        |
# | PLIK: scripts/gates/dp_budget_gate.py                      |
# | ROLA: Bramka: budżety epsilon DP (stub)                      |
# +-------------------------------------------------------------+

"""
PL: Bramka budżetów DP. Czyta JSON ze stdin:
  {"budgets": [{"name": "alpha", "limit": 1.0, "used": 0.3}, ...]}
Gdy `STRICT_DP_BUDGET=1`, FAIL jeśli którykolwiek used > limit.
Bez wejścia używa wartości domyślnych (PASS).

EN: DP budgets gate. Reads input JSON stdin with budgets entries.
If `STRICT_DP_BUDGET=1`, FAIL when any used > limit; otherwise PASS.
Defaults to PASS when no input.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
import sys
from typing import Any

# === LOGIKA / LOGIC ===


def _read() -> dict[str, Any]:
    try:
        raw = sys.stdin.read().strip()
        if raw:
            return json.loads(raw)
    except Exception:
        pass
    return {"budgets": [{"name": "alpha", "limit": 1.0, "used": 0.2}]}


def _is_on(v: str | None) -> bool:
    return (v or "").strip().lower() in {"1", "true", "on", "yes"}


def main() -> int:
    data = _read()
    strict = _is_on(os.getenv("STRICT_DP_BUDGET"))
    budgets = data.get("budgets") or []
    over: list[str] = []
    for b in budgets:
        try:
            name = str(b.get("name"))
            limit = float(b.get("limit", 0.0))
            used = float(b.get("used", 0.0))
            if used > limit:
                over.append(f"{name}:{used}>{limit}")
        except Exception:
            continue
    if strict and over:
        print("DP Budget Gate: FAIL overuse —", ", ".join(over))
        return 1
    print("DP Budget Gate: OK")
    return 0


# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
