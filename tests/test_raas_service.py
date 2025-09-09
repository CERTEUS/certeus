#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/test_raas_service.py                            |
# | ROLE: Unit tests for RAaaS                                  |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path

from fastapi.testclient import TestClient

from certeus.services.raas_service.main import app


def test_ra_get_attestation_from_file(tmp_path: Path, monkeypatch) -> None:
    att = {"vendor": "test", "product": "sim", "claims": {"a": 1}}
    p = tmp_path / "att.json"
    p.write_text(json.dumps(att), encoding="utf-8")
    monkeypatch.setenv("BUNKER_ATTESTATION_PATH", str(p))

    c = TestClient(app)
    r = c.get("/v1/ra/attestation")
    assert r.status_code == 200
    body = r.json()
    assert body["claims"]["a"] == 1


def test_ra_verify_roundtrip() -> None:
    c = TestClient(app)
    att = {"claims": {"x": 7, "y": "ok"}}
    r = c.post("/v1/ra/verify", json=att)
    assert r.status_code == 200
    fp = r.json()
    assert fp["vendor"]
    assert fp["product"]
    assert isinstance(fp["measurement"], str) and len(fp["measurement"]) == 64
