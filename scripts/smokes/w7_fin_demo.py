#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w7_fin_demo.py                        |
# | ROLE: Week 7 FIN demo (measure/mi/sim/pnl).                 |
# | PLIK: scripts/smokes/w7_fin_demo.py                        |
# | ROLA: Demo tyg. 7 FIN (measure/mi/sim/pnl).                 |
# +-------------------------------------------------------------+
"""
PL: Demo W7 — FIN endpoints: measure, entanglement/mi, simulate, pnl.
EN: Week-7 demo — FIN endpoints: measure, entanglement/mi, simulate, pnl.
"""

from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    out = Path("reports/w7_fin_demo.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    c = TestClient(app)
    r_m = c.post("/v1/fin/alpha/measure", json={"signals": {"risk": 0.2, "sentiment": 0.5}})
    r_m.raise_for_status()
    r_mi = c.post(
        "/v1/fin/alpha/entanglement/mi",
        json=[{"a": "A", "b": "B", "series_a": [0.1, 0.2, 0.3], "series_b": [0.15, 0.22, 0.31]}],
    )
    r_mi.raise_for_status()
    r_s = c.post(
        "/v1/fin/alpha/simulate",
        json={"strategy_id": "qalpha-momentum", "capital": 100000, "horizon_days": 30},
        headers={"X-Tenant-ID": "fin-demo"},
    )
    r_s.raise_for_status()
    r_pnl = c.get("/v1/fin/alpha/pnl", headers={"X-Tenant-ID": "fin-demo"})
    r_pnl.raise_for_status()
    out.write_text(
        json.dumps(
            {
                "measure": r_m.json(),
                "mi": r_mi.json(),
                "simulate": r_s.json(),
                "pnl": r_pnl.json(),
            },
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"Saved {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
