#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w3_geometry_demo.py                    |
# | ROLE: Week 3 demo — CFE Geometry (geodesic/horizon)         |
# | PLIK: scripts/smokes/w3_geometry_demo.py                    |
# | ROLA: Demo Tygodnia 3 — CFE Geometry (geodezje/horyzont)    |
# +-------------------------------------------------------------+
"""
PL: Demo W3 — CFE: geodezyjna ścieżka i horyzont, PCO nagłówki i wpis do Księgi.
EN: Week-3 demo — CFE: geodesic path and horizon, PCO headers and Ledger entry.
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
    case_id = "LEX-001-sample"

    r_cur = c.get("/v1/cfe/curvature", params={"case_id": case_id})
    r_cur.raise_for_status()
    _pp("Curvature", r_cur.json())

    r_geo = c.post("/v1/cfe/geodesic", json={"case": case_id, "facts": {}, "norms": {}})
    r_geo.raise_for_status()
    hdr_geo = r_geo.headers.get("X-CERTEUS-PCO-cfe.geodesic_action")
    _pp("Geodesic", {"body": r_geo.json(), "pco_header": hdr_geo})

    r_hz = c.post("/v1/cfe/horizon", json={"case": case_id, "lock": True})
    r_hz.raise_for_status()
    hdr_mass = r_hz.headers.get("X-CERTEUS-PCO-cfe.horizon_mass")
    hdr_locked = r_hz.headers.get("X-CERTEUS-CFE-Locked")
    _pp("Horizon", {"body": r_hz.json(), "mass": hdr_mass, "locked": hdr_locked})

    # Verify ledger entries exist for the case
    r_log = c.get(f"/v1/ledger/{case_id}/records")
    r_log.raise_for_status()
    entries = r_log.json()
    _pp("Ledger entries", {"case": case_id, "count": len(entries)})

    print("\nOK: Week-3 demo complete (Geometry: geodesic + horizon + ledger)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

