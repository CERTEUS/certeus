#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lex_micro_court.py               |
# | ROLE: LEX Micro‑Court pipeline tests                         |
# | PLIK: tests/services/test_lex_micro_court.py               |
# | ROLA: Testy potoku Micro‑Court (lock→publish, PCO ścieżki)   |
# +-------------------------------------------------------------+

"""
PL: W6 — testuje lock→publish z PCO ścieżki i ledger record (best-effort).

EN: W6 — tests lock→publish with path PCO and best-effort ledger record.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_micro_court_lock_and_publish() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    case = "LEX-W6-001"

    r = c.post("/v1/lexenith/micro_court/lock", json={"case_id": case})
    assert r.status_code == 200
    js = r.json()
    assert js.get("locked") and js.get("case_id") == case
    assert "X-CERTEUS-PCO-lex.micro_court" in r.headers

    r = c.post(
        "/v1/lexenith/micro_court/publish",
        json={"case_id": case, "footnotes": ["Hash this footnote"]},
    )
    assert r.status_code == 200
    js = r.json()
    assert js.get("published") and js.get("case_id") == case
    path = js.get("path")
    assert isinstance(path, list) and any(
        step.get("step") == "publish" for step in path
    )
