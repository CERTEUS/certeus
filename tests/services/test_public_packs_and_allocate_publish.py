#!/usr/bin/env python3
"""
PL: W13 — public packs (lex_casebook, fin_policy) + allocate→publish ścieżka.
EN: W13 — public packs (lex_casebook, fin_policy) + allocate→publish path.
"""

from __future__ import annotations

from fastapi.testclient import TestClient


def test_public_packs_and_allocate_publish_roundtrip(monkeypatch) -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    # Seed casebook with one case
    cid = "LEX-PACK-001"
    c.post("/v1/lexenith/micro_court/lock", json={"case_id": cid})
    c.post("/v1/lexenith/micro_court/publish", json={"case_id": cid})

    # lex_casebook pack
    r = c.post(
        "/v1/packs/handle",
        json={"pack": "lex_casebook", "kind": "lex.casebook.latest", "payload": {"limit": 1}},
    )
    assert r.status_code == 200 and r.json().get("ok") is True
    assert r.json()["result"].get("count", 0) >= 1

    # fin_policy pack
    r = c.post(
        "/v1/packs/handle",
        json={
            "pack": "fin_policy",
            "kind": "fin.policy.check",
            "payload": {"signals": {"risk": 0.5, "sentiment": 0.2}},
        },
    )
    assert r.status_code == 200 and r.json().get("ok") is True
    assert r.json()["result"].get("policy_ok") is True

    # allocate→publish (budget_tokens)
    r = c.post("/v1/billing/quota", json={"tenant": "packs-demo", "units": 10})
    assert r.status_code == 200
    r = c.post("/v1/billing/allocate", json={"units": 2}, headers={"X-Tenant-ID": "packs-demo"})
    assert r.status_code == 200
    # disable strict proof-only for this publish alias test (we only exercise billing path)
    monkeypatch.setenv("STRICT_PROOF_ONLY", "0")
    r = c.post(
        "/defx/reason",
        json={"pco": {"ok": True}, "budget_tokens": 2},
        headers={"X-Tenant-ID": "packs-demo"},
    )
    assert r.status_code == 200 and r.json().get("status") == "PENDING"
