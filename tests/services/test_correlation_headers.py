#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_correlation_headers.py           |
# | ROLE: Tests for correlation/trace headers                    |
# | PLIK: tests/services/test_correlation_headers.py           |
# | ROLA: Testy nagłówków korelacji/trace                        |
# +-------------------------------------------------------------+
"""
PL: Weryfikuje, że odpowiedzi zawierają `X-Correlation-ID` oraz bezpieczne
    nagłówki PCO korelacji. OTel może być nieaktywny — test nie wymaga trace.

EN: Verifies responses include `X-Correlation-ID` and safe PCO correlation
    headers. OTel may be inactive — test does not require trace.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_correlation_headers_present() -> None:
    from services.api_gateway.main import app

    client = TestClient(app)
    r = client.get("/health")
    assert r.status_code == 200
    # Base correlation header
    assert r.headers.get("X-Correlation-ID")
    # PCO bridge header
    assert r.headers.get("X-CERTEUS-PCO-correlation.correlation_id")
    # Trace headers are optional; if present, must be hex
    tid = r.headers.get("X-Trace-Id")
    if tid:
        assert all(c in "0123456789abcdef" for c in tid.lower())


# === TESTY / TESTS ===
