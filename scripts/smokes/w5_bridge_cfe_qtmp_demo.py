#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w5_bridge_cfe_qtmp_demo.py             |
# | ROLE: Week 5 demo — CFE↔QTMP Bridge                         |
# | PLIK: scripts/smokes/w5_bridge_cfe_qtmp_demo.py             |
# | ROLA: Demo Tygodnia 5 — Most CFE↔QTMP                       |
# +-------------------------------------------------------------+
"""
PL: Demo W5 — Most CFE↔QTMP: pobierz kappa_max (CFE), wykonaj QTMP measure
    i pokaż korelację oraz priorytety L/T (delta vs 1.0).

EN: Week-5 demo — CFE↔QTMP bridge: fetch kappa_max (CFE), run QTMP measure,
    and display correlation and L/T priorities (delta vs 1.0).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json


def _ensure_repo_on_path() -> None:
    from pathlib import Path as _P
    import sys as _sys

    _sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402


_ensure_repo_on_path()

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app as gateway_app  # noqa: E402


def _pp(title: str, data) -> None:
    print(f"\n== {title} ==")
    try:
        print(json.dumps(data, indent=2, ensure_ascii=False))
    except Exception:
        print(str(data))


def main() -> int:
    c = TestClient(gateway_app)
    case = "W5-bridge"
    r_k = c.get("/v1/cfe/curvature", params={"case_id": case})
    r_k.raise_for_status()
    kappa = float(r_k.json().get("kappa_max", 0.0))
    _pp("CFE curvature", r_k.json())

    r_m = c.post("/v1/qtm/measure", json={"operator": "LT", "source": case})
    r_m.raise_for_status()
    hdr = r_m.headers
    corr = hdr.get("X-CERTEUS-PCO-correlation.cfe_qtmp")
    pri_raw = hdr.get("X-CERTEUS-PCO-qtmp.priorities") or "{}"
    try:
        pri = json.loads(pri_raw)
    except Exception:
        pri = {}
    dL = (float(pri.get("L", 1.0)) - 1.0) if pri else 0.0
    dT = (float(pri.get("T", 1.0)) - 1.0) if pri else 0.0
    _pp(
        "QTMP measure",
        {"corr": corr, "priorities": pri, "delta_L": dL, "delta_T": dT, "kappa": kappa},
    )
    print("\nOK: Week-5 CFE↔QTMP bridge demo complete")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
