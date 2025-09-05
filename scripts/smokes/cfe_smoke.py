#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/cfe_smoke.py                          |
# | ROLE: Project script.                                       |
# | PLIK: scripts/smokes/cfe_smoke.py                          |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: In-proc smoke dla CFE: curvature, lensing, warm cache, lensing/from_fin.
EN: In-proc smoke for CFE: curvature, lensing, warm cache, lensing/from_fin.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path
import sys


def _ensure_path() -> None:
    root = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(root))


def main() -> int:
    _ensure_path()
    from fastapi.testclient import TestClient

    from services.api_gateway.main import app

    c = TestClient(app)
    out: dict[str, object] = {}

    r1 = c.get("/v1/cfe/curvature?case_id=SMOKE-1")
    out["curvature"] = r1.json() if r1.status_code == 200 else {"error": r1.status_code}

    _ = c.post("/v1/cfe/cache/warm", json=["SMOKE-1", "SMOKE-2"]).json()

    r2 = c.get("/v1/cfe/lensing?case_id=SMOKE-2")
    out["lensing"] = r2.json() if r2.status_code == 200 else {"error": r2.status_code}

    r3 = c.post(
        "/v1/cfe/lensing/from_fin",
        json={"signals": {"risk": 0.2, "sentiment": 0.6}, "seed": "SMOKE-FIN"},
    )
    out["from_fin"] = r3.json() if r3.status_code == 200 else {"error": r3.status_code}

    import json as _json

    print(_json.dumps(out, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
