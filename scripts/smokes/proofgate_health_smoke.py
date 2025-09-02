#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/proofgate_health_smoke.py             |
# | ROLE: Smoke: ProofGate /healthz                              |
# | PLIK: scripts/smokes/proofgate_health_smoke.py             |
# | ROLA: Smoke: ProofGate /healthz                              |
# +-------------------------------------------------------------+

"""
PL: Smoke testuje endpoint `/healthz` ProofGate in-proc.
EN: Smoke for ProofGate `/healthz` in-proc.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.proofgate.app import app


# === LOGIKA / LOGIC ===
def main() -> int:
    c = TestClient(app)
    r = c.get("/healthz")
    if r.status_code != 200:
        print("ProofGate /healthz: FAIL", r.status_code)
        return 1
    if not (r.json() or {}).get("ok", False):
        print("ProofGate /healthz: FAIL body")
        return 1
    print("ProofGate /healthz: OK")
    return 0


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
