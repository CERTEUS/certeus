#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_tunnel.py                |
# | ROLE: Project module.                                       |
# | PLIK: tests/services/test_lexqft_tunnel.py                |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Scenariusze testowe dla /v1/lexqft/tunnel (D21):
 - niski poziom energii (niska szansa tunelowania)
 - wysoki poziom energii (wysoka szansa tunelowania)
W obu przypadkach oczekujemy nagłówków PCO qlaw.tunneling.*.

EN: Test scenarios for /v1/lexqft/tunnel (D21):
 - low evidence energy (low tunneling probability)
 - high energy (high probability)
Expect PCO headers qlaw.tunneling.* in both cases.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_tunnel_low_energy_has_pco_headers() -> None:
    r = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": 0.2, "state_uri": "psi://case-low"},
    )
    assert r.status_code == 200
    body = r.json()
    assert 0.05 <= body["p_tunnel"] <= 0.2
    # PCO headers present
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.p") is not None
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.path") is not None
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.min_energy") is not None


def test_tunnel_high_energy_has_high_p_and_pco_headers() -> None:
    r = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": 1.2, "state_uri": "psi://case-high"},
    )
    assert r.status_code == 200
    body = r.json()
    assert body["p_tunnel"] >= 0.9
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.p") is not None
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.path") is not None
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.min_energy") is not None
