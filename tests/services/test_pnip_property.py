from __future__ import annotations

import string

from fastapi.testclient import TestClient
from hypothesis import HealthCheck, given, settings, strategies as st

hex_chars = st.text(alphabet=st.sampled_from(list(string.hexdigits.lower())), min_size=64, max_size=64)


@settings(max_examples=20)
@given(valid_hex=hex_chars)
def test_pnip_strict_accepts_valid_sha256_and_policy(valid_hex: str) -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    hdrs = {"X-Policy-Pack-ID": "pco-policy-pack", "X-Jurisdiction": "PL:lex"}
    r = c.post(
        "/v1/ledger/record-input",
        json={"case_id": "P-OK", "document_hash": f"sha256:{valid_hex[:64]}"},
        headers=hdrs,
    )
    # Z poprawnym hashem i właściwym policy id powinno przejść
    assert r.status_code in (200, 201)


@settings(max_examples=10, suppress_health_check=[HealthCheck.function_scoped_fixture])
@given(bad_hash=st.just("sha1:" + ("0" * 8)))
def test_pnip_strict_rejects_invalid_hash_when_enabled(bad_hash: str, monkeypatch) -> None:
    from services.api_gateway.main import app

    monkeypatch.setenv("STRICT_PNIP", "1")
    c = TestClient(app)
    r = c.post(
        "/v1/ledger/record-input",
        json={"case_id": "P-BAD", "document_hash": bad_hash},
        headers={"X-Policy-Pack-ID": "WRONG", "X-Jurisdiction": "PL:lex"},
    )
    assert r.status_code == 400
