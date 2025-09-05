#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_mailops_smoke.py                 |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_mailops_smoke.py                 |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Lekki smoke test dla /v1/mailops/ingest (MVP z W1 D3).

EN: Lightweight smoke test for /v1/mailops/ingest (W1 D3 MVP).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_mailops_ingest_smoke() -> None:
    # Import po to, aby zarejestrować wszystkie routery
    from services.api_gateway.main import app

    client = TestClient(app)

    payload = {
        "mail_id": "MAIL-001",
        "from_addr": "sender@example.com",
        "to": ["recipient@example.com"],
        "subject": "Smoke",
        "body_text": "Hello",
        "attachments": [],
    }

    r = client.post("/v1/mailops/ingest", json=payload)
    assert r.status_code == 200
    data = r.json()
    assert data.get("ok") is True
    io = data.get("io") or {}
    assert io.get("io.email.mail_id") == "MAIL-001"


# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
