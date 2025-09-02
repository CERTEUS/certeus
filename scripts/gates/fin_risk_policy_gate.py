#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/fin_risk_policy_gate.py               |
# | ROLE: Project gate script.                                   |
# | PLIK: scripts/gates/fin_risk_policy_gate.py               |
# | ROLA: Skrypt bramki projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Bramka FIN ryzyka (proxy OPA/Rego). Weryfikuje dwie polityki:
 - risk_limit: risk <= 0.7
 - signals_dp: dp_epsilon <= 1.0 (i obecny)
Wejście: JSON (stdin) lub wartości domyślne.

EN: FIN risk gate (OPA/Rego proxy). Verifies two policies:
 - risk_limit: risk <= 0.7
 - signals_dp: dp_epsilon present and <= 1.0
Input: JSON (stdin) or defaults.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import sys
from typing import Any


def _read_input() -> dict[str, Any]:
    try:
        data = sys.stdin.read().strip()
        if data:
            return json.loads(data)
    except Exception:
        pass
    # defaults
    return {"signals": {"risk": 0.5, "sentiment": 0.6}, "dp_epsilon": 0.3}


def main() -> int:
    inp = _read_input()
    signals = inp.get("signals") or {}
    risk = float(signals.get("risk", 0.0))
    dp_eps = float(inp.get("dp_epsilon", 10.0)) if inp.get("dp_epsilon") is not None else None

    errs: list[str] = []

    # risk_limit.rego equivalent
    if risk > 0.7:
        errs.append(f"risk too high: {risk}")

    # signals_dp.rego equivalent
    if dp_eps is None:
        errs.append("missing dp_epsilon")
    elif dp_eps > 1.0:
        errs.append(f"dp_epsilon too high: {dp_eps}")

    if errs:
        print("FIN Risk Gate: FAIL", "; ".join(errs))
        return 1

    print("FIN Risk Gate: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
