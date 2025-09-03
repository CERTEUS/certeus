#!/usr/bin/env python3
"""
PL: Property tests dla /v1/marketplace/dry_run (nazwy i semver).
EN: Property tests for /v1/marketplace/dry_run (names and semver).
"""

from __future__ import annotations

from fastapi.testclient import TestClient
from hypothesis import HealthCheck, given, settings, strategies as st

from services.api_gateway.main import app


def _req(name: str, module: str = "plugins.x.src.main", version: str = "0.1.0") -> dict:
    return {
        "name": name,
        "manifest_yaml": f"name: {name}\nmodule: {module}\nversion: '{version}'\n",
        "signature_b64u": "b64u",  # zostanie odrzucone jako invalid_signature, to akceptujemy w teście dry_run
    }


@settings(max_examples=25, suppress_health_check=[HealthCheck.too_slow])
@given(st.text(min_size=1, max_size=10))
def test_dry_run_rejects_bad_names(name: str):
    c = TestClient(app)
    # wstrzyknij niedozwolone znaki
    bad = name + "../"
    r = c.post("/v1/marketplace/dry_run", json=_req(bad))
    assert r.status_code == 200
    body = r.json()
    assert "invalid_name" in (body.get("errors") or [])


@settings(max_examples=25, suppress_health_check=[HealthCheck.too_slow])
@given(st.from_regex(r"\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?", fullmatch=True))
def test_dry_run_accepts_semver(version: str):
    c = TestClient(app)
    r = c.post("/v1/marketplace/dry_run", json=_req("safe_name", version=version))
    assert r.status_code == 200
    body = r.json()
    # może mieć invalid_signature, ale nie invalid_version_semver
    assert "invalid_version_semver" not in (body.get("errors") or [])
