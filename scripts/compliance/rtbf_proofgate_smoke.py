#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/compliance/rtbf_proofgate_smoke.py          |
# | ROLE: ProofGate RTBF smoke (appeal/erase endpoints)         |
# | PLIK: scripts/compliance/rtbf_proofgate_smoke.py          |
# | ROLA: Smoke RTBF ProofGate (appeal/erase endpointy)         |
# +-------------------------------------------------------------+

"""
PL: Smoke ProofGate RTBF: /v1/rtbf/appeal, /v1/rtbf/erase, /v1/rtbf/erased/{case}
EN: ProofGate RTBF smoke for appeal/erase endpoints.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path
import sys

from fastapi.testclient import TestClient


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    if str(repo) not in sys.path:
        sys.path.insert(0, str(repo))

    from services.proofgate.app import app  # noqa: E402

    case = "CER-LEX-RTBF-DEMO"
    with TestClient(app) as c:
        r1 = c.post("/v1/rtbf/appeal", json={"case_id": case, "reason": "user_request"})
        r2 = c.post("/v1/rtbf/erase", json={"case_id": case})
        r3 = c.get(f"/v1/rtbf/erased/{case}")

    ok = (
        (r1.status_code == 200 and r1.json().get("status") == "RECEIVED")
        and (r2.status_code == 200 and r2.json().get("status") == "ERASED")
        and (r3.status_code == 200 and r3.json().get("erased") is True)
    )

    print(json.dumps({"ok": ok}))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
