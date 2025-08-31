#!/usr/bin/env python3
from __future__ import annotations

from fastapi.testclient import TestClient

from services.ledger_service.ledger import ledger_service
from services.proofgate.app import app

client = TestClient(app)


def test_publish_when_risk_within_thresholds_and_budget() -> None:
    pco = {
        "case_id": "case-123",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
    }
    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
    assert r.status_code == 200, r.text
    body = r.json()
    assert body["status"] == "PUBLISH"
    assert isinstance(body.get("ledger_ref"), str) and len(body["ledger_ref"]) == 64
    # Verify ledger has a record for this case
    records = ledger_service.get_records_for_case(case_id="case-123")
    assert any(rec.get("type") == "PCO_PUBLISH" and rec.get("chain_self") == body["ledger_ref"] for rec in records)


def test_abstain_when_any_risk_exceeds() -> None:
    pco = {
        "risk": {"ece": 0.03, "brier": 0.05, "abstain_rate": 0.05},
    }
    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
    assert r.status_code == 200, r.text
    assert r.json()["status"] == "ABSTAIN"


def test_pending_when_no_budget_but_good_risk() -> None:
    pco = {
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
    }
    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 0})
    assert r.status_code == 200, r.text
    assert r.json()["status"] == "PENDING"


def test_conditional_when_missing_risk() -> None:
    pco = {"something_else": True}
    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 5})
    assert r.status_code == 200, r.text
    assert r.json()["status"] == "CONDITIONAL"
