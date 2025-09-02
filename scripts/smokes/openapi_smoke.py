#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/openapi_smoke.py                      |
# | ROLE: Smoke: API Gateway /openapi.json                       |
# | PLIK: scripts/smokes/openapi_smoke.py                      |
# | ROLA: Smoke: /openapi.json Gateway                            |
# +-------------------------------------------------------------+

"""
PL: Smoke sprawdzający poprawność `/openapi.json` w trybie in‑proc.
EN: Smoke that validates `/openapi.json` in-process.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


# === LOGIKA / LOGIC ===
def main() -> int:
    c = TestClient(app)
    r = c.get("/openapi.json")
    if r.status_code != 200:
        print("OpenAPI smoke: FAIL status", r.status_code)
        return 1
    try:
        data = r.json()
    except Exception:
        print("OpenAPI smoke: FAIL invalid JSON")
        return 1
    if not isinstance(data, dict) or "openapi" not in data or "paths" not in data:
        print("OpenAPI smoke: FAIL missing keys")
        return 1
    print("OpenAPI smoke: OK")
    return 0


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
