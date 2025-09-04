#!/usr/bin/env python3

"""
PL: Test sprawdzający, że MailOps /ingest nadaje URI ProofFS dla załączników.
EN: Test verifying MailOps /ingest adds ProofFS URIs to attachments.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_mailops_ingest_returns_pfs_uri() -> None:
    client = TestClient(app)
    payload = {
        "mail_id": "MID-TEST",
        "thread_id": "T-TEST",
        "from_addr": "a@example.com",
        "to": ["b@example.com"],
        "subject": "Hello",
        "body_text": "Hi",
        "attachments": [{"filename": "file.pdf", "content_type": "application/pdf", "size": 10}],
    }
    r = client.post("/v1/mailops/ingest", json=payload)
    assert r.status_code == 200
    data = r.json()
    atts = data.get("io", {}).get("attachments", [])
    assert atts and isinstance(atts[0], dict)
    pfs_uri = atts[0].get("pfs_uri", "")
    assert pfs_uri.startswith("pfs://mail/MID-TEST/")
