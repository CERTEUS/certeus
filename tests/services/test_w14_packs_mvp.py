#!/usr/bin/env python3
"""
PL: W14 — 3 packi demo (MED/SEC/CODE): proste wywołania handle przez /v1/packs.
EN: W14 — 3 demo packs (MED/SEC/CODE): simple handle calls via /v1/packs.
"""

from __future__ import annotations

from fastapi.testclient import TestClient


def test_med_phi_redact_pack() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post(
        "/v1/packs/handle",
        json={"pack": "med_demo", "kind": "med.phi.redact", "payload": {"text": "PESEL: 123 DOB: 2001-01-01"}},
    )
    assert r.status_code == 200
    body = r.json().get("result") or {}
    assert "[REDACTED]" in body.get("redacted", "")


def test_sec_risk_assess_pack() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.post(
        "/v1/packs/handle",
        json={"pack": "sec_demo", "kind": "sec.risk.assess", "payload": {"vulns": ["a", "b", "c"]}},
    )
    assert r.status_code == 200
    body = r.json().get("result") or {}
    assert body.get("risk_grade") in {"LOW", "MEDIUM", "HIGH"}


def test_code_static_check_pack() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    src = "line1\n# TODO: refactor\npass\n"
    r = c.post(
        "/v1/packs/handle",
        json={"pack": "code_demo", "kind": "code.static.check", "payload": {"source": src}},
    )
    assert r.status_code == 200
    body = r.json().get("result") or {}
    assert body.get("lines") >= 3 and body.get("todo") >= 1
