#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w4_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w4_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W4 — QTMP demo: init_case → set decoherence → measure L→T i T→L,
    porównanie rozkładów (kolejność wpływa na wynik).

EN: W4 — QTMP demo: init_case → set decoherence → measure L→T and T→L,
    compare distributions (order affects the result).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    c = TestClient(app)
    case = "LEX-W4-DEMO"
    # Init and set decoherence to a visible value
    c.post(
        "/v1/qtm/init_case", json={"case": case, "basis": ["ALLOW", "DENY", "ABSTAIN"]}
    )
    c.post(
        "/v1/qtm/decoherence", json={"case": case, "channel": "dephasing", "gamma": 0.2}
    )
    # Run sequence L->T
    r_lt = c.post(
        "/v1/qtm/measure_sequence", json={"operators": ["L", "T"], "case": case}
    )
    # Run sequence T->L
    r_tl = c.post(
        "/v1/qtm/measure_sequence", json={"operators": ["T", "L"], "case": case}
    )
    lt_p = [
        float(s.get("p", 0.0))
        for s in (r_lt.json().get("steps", []) if r_lt.status_code == 200 else [])
    ]
    tl_p = [
        float(s.get("p", 0.0))
        for s in (r_tl.json().get("steps", []) if r_tl.status_code == 200 else [])
    ]
    # Simple difference metric: abs diff of last step probability
    d = 0.0
    if lt_p and tl_p:
        d = abs(lt_p[-1] - tl_p[-1])
    rep = {
        "case": case,
        "lt_probs": lt_p,
        "tl_probs": tl_p,
        "diff_last": d,
        "uncertainty_lt": (
            r_lt.json().get("uncertainty_bound", {}).get("L_T")
            if r_lt.status_code == 200
            else None
        ),
        "uncertainty_tl": (
            r_tl.json().get("uncertainty_bound", {}).get("L_T")
            if r_tl.status_code == 200
            else None
        ),
    }
    Path("reports").mkdir(parents=True, exist_ok=True)
    Path("reports/w4_demo.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {"ok": r_lt.ok and r_tl.ok if hasattr(r_lt, "ok") else True, "diff_last": d}
        )
    )
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
