# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/qtm_smoke.py                           |
# | ROLE: In-proc smoke for QTMP endpoints                      |
# | PLIK: scripts/smokes/qtm_smoke.py                           |
# | ROLA: Smoke in-proc dla endpointów QTMP                     |
# +-------------------------------------------------------------+

"""
PL: Szybki smoke: init_case, measure, operators, uncertainty.
EN: Quick smoke test: init_case, measure, operators, uncertainty.
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
    r = c.post("/v1/qtm/init_case", json={"case": "SMOKE-QTMP", "basis": ["ALLOW", "DENY", "ABSTAIN"]})
    assert r.status_code == 200
    r2 = c.post("/v1/qtm/measure", json={"operator": "L", "source": "ui", "case": "SMOKE-QTMP"})
    assert r2.status_code == 200
    assert "X-CERTEUS-PCO-qtm.collapse_event" in r2.headers
    r3 = c.get("/v1/qtm/operators")
    assert r3.status_code == 200
    r4 = c.get("/v1/qtm/uncertainty")
    assert r4.status_code == 200
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

