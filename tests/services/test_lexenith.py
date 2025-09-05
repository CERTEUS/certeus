#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexenith.py                     |
# | ROLE: Project module.                                       |
# | PLIK: tests/services/test_lexenith.py                     |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Smoke testy dla LEXENITH: motion/generate (PCO), cldf/renormalize,
    why_not/export.

EN: Smoke tests for LEXENITH endpoints: motion/generate (PCO),
    cldf/renormalize, why_not/export.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

client = TestClient(app)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

def test_motion_generate_pco_header() -> None:
    r = client.post(
        "/v1/lexenith/motion/generate",
        json={
            "case_id": "LEX-CASE-1",
            "pattern_id": "motion-dismiss",
            "citations": ["Art. 5 k.c."],
            "facts": {"A": 1},
        },
    )
    assert r.status_code == 200
    assert r.headers.get("X-CERTEUS-PCO-lex.motion.citations") is not None
    body = r.json()
    assert isinstance(body.get("document"), str)
    assert body.get("citations") and body["citations"][0]["hash"]

def test_cldf_renormalize() -> None:
    arr = [
        {"text": "I CSK 123/20", "weight": 1.0},
        {"text": "III 2020", "weight": 0.5},
    ]
    r = client.post("/v1/lexenith/cldf/renormalize", json={"citations": arr})
    assert r.status_code == 200
    body = r.json()
    assert body.get("normalized") is True
    cites = body.get("citations")
    assert isinstance(cites, list) and len(cites) == 2
    assert "authority_score" in cites[0]

def test_why_not_export() -> None:
    r = client.post(
        "/v1/lexenith/why_not/export",
        json={"claim": "Powództwo o zapłatę", "counter_arguments": ["brak legitymacji"]},
    )
    assert r.status_code == 200
    body = r.json()
    assert body.get("ok") is True
    assert str(body.get("trace_uri", "")).startswith("pfs://why-not/")
