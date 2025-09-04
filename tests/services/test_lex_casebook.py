#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lex_casebook.py                  |
# | ROLE: LEX casebook tests                                      |
# | PLIK: tests/services/test_lex_casebook.py                  |
# | ROLA: Testy casebook (ostatnie sprawy Micro‑Court)            |
# +-------------------------------------------------------------+

"""
PL: W12 — Casebook: po 3 publikacjach, endpoint zwraca ≥3 sprawy (newest‑first).

EN: W12 — Casebook: after 3 publishes, endpoint returns ≥3 cases (newest‑first).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_lex_casebook_lists_latest_three_cases() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    cases = ["LEX-CB-001", "LEX-CB-002", "LEX-CB-003"]
    for cid in cases:
        c.post("/v1/lexenith/micro_court/lock", json={"case_id": cid})
        r = c.post("/v1/lexenith/micro_court/publish", json={"case_id": cid, "footnotes": ["note"]})
        assert r.status_code == 200

    r = c.get("/v1/lexenith/casebook")
    assert r.status_code == 200
    js = r.json()
    items = js.get("cases")
    assert isinstance(items, list) and len(items) >= 3
    # newest-first ordering
    got_ids = [it.get("case_id") for it in items[:3]]
    assert got_ids == list(reversed(cases))
