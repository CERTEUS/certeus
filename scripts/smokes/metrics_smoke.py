#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/metrics_smoke.py                      |
# | ROLE: Smoke: Prometheus /metrics endpoint                    |
# | PLIK: scripts/smokes/metrics_smoke.py                      |
# | ROLA: Smoke: endpoint /metrics Prometheus                     |
# +-------------------------------------------------------------+

"""
PL: Prosty smoke sprawdzający, że /metrics zwraca niepustą odpowiedź i
    zawiera kluczowe metryki (np. "certeus_http_request_duration_ms").

EN: Simple smoke that /metrics responds and contains key metrics
    (e.g., "certeus_http_request_duration_ms").
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


# === LOGIKA / LOGIC ===
def main() -> int:
    client = TestClient(app)
    r = client.get("/metrics")
    if r.status_code != 200:
        print("/metrics: FAIL status", r.status_code)
        return 1
    text = r.text or ""
    if "certeus_http_request_duration_ms" not in text:
        print("/metrics: FAIL missing histogram certeus_http_request_duration_ms")
        return 1
    print("/metrics: OK")
    return 0


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
