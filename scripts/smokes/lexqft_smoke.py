#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/lexqft_smoke.py                        |
# | ROLE: In-proc smoke for LexQFT coverage                     |
# | PLIK: scripts/smokes/lexqft_smoke.py                        |
# | ROLA: Smoke in-proc dla LexQFT coverage                     |
# +-------------------------------------------------------------+

"""
PL: Smoke: reset, update i state dla LexQFT coverage.
EN: Smoke: reset, update and state for LexQFT coverage.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import sys

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    c = TestClient(app)
    c.post("/v1/lexqft/coverage/reset")
    items = [
        {"gamma": 0.9, "weight": 2.0, "uncaptured": 0.05},
        {"gamma": 0.7, "weight": 1.0, "uncaptured": 0.15},
    ]
    r = c.post("/v1/lexqft/coverage/update", json=items)
    assert r.status_code == 200
    rs = c.get("/v1/lexqft/coverage/state")
    assert rs.status_code == 200
    body = rs.json()
    assert 0.83 <= float(body.get("coverage_gamma", 0.0)) <= 0.84
    assert 0.08 <= float(body.get("uncaptured_mass", 0.0)) <= 0.09
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
