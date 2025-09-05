# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/qtm_seq_expect_smoke.py                |
# | ROLE: In-proc smoke for QTMP sequence + expectation         |
# | PLIK: scripts/smokes/qtm_seq_expect_smoke.py                |
# | ROLA: Smoke in-proc sekwencji + expectation QTMP            |
# +-------------------------------------------------------------+

"""
PL: Smoke: measure_sequence oraz expectation na bazie stanu.
EN: Smoke: measure_sequence and expectation based on state.
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
    case = "SMOKE-QTMP-SEQ"
    # Set state
    r = c.post(
        "/v1/qtm/state",
        json={"case": case, "basis": ["ALLOW", "DENY", "ABSTAIN"], "probs": [0.6, 0.3, 0.1]},
    )
    assert r.status_code == 200
    # Sequence
    r2 = c.post("/v1/qtm/measure_sequence", json={"case": case, "operators": ["L", "T", "W"]})
    assert r2.status_code == 200
    assert "X-CERTEUS-PCO-qtm.sequence" in r2.headers
    # Expectation
    r3 = c.post("/v1/qtm/expectation", json={"case": case, "operator": "W"})
    assert r3.status_code == 200
    assert "value" in r3.json()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
