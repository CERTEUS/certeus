#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_tunnel.py                 |
# | ROLE: LexQFT tunneling tests (barrier model + PCO headers) |
# | PLIK: tests/services/test_lexqft_tunnel.py                 |
# | ROLA: Testy tunelowania LexQFT (bariera + nagłówki PCO)    |
# +-------------------------------------------------------------+

"""
PL: Testy endpointu /v1/lexqft/tunnel: wariant domyślny oraz z
    `barrier_model` (energia bariery) i nagłówkami PCO.
EN: Tests for /v1/lexqft/tunnel: default behavior and with a
    `barrier_model` (barrier energy) and PCO headers.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)

def test_tunnel_default_high_energy_pass() -> None:
    r = client.post(
        "/v1/lexqft/tunnel",
        json={"evidence_energy": 1.2},
    )
    assert r.status_code == 200
    body = r.json()
    assert body["p_tunnel"] == 0.95
    assert body["path"] and body["path"][-1] in {"post-barrier", "reflect"}
    # PCO headers present
    assert "X-CERTEUS-PCO-qlaw.tunneling.p" in r.headers
    assert "X-CERTEUS-PCO-qlaw.tunneling.min_energy" in r.headers

def test_tunnel_with_barrier_energy_reflect_case() -> None:
    barrier_energy = 1.5
    evidence = 1.0
    expected_p = max(0.05, (evidence / barrier_energy) * 0.6)
    r = client.post(
        "/v1/lexqft/tunnel",
        json={
            "evidence_energy": evidence,
            "barrier_model": {"energy": barrier_energy, "model_uri": "lexqft://barrier/demo"},
        },
    )
    assert r.status_code == 200
    body = r.json()
    assert abs(body["p_tunnel"] - expected_p) < 1e-6
    assert body["path"][-1] == "reflect"
    # PCO headers include p, path and min energy, plus optional model uri
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.p") is not None
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.min_energy") == str(barrier_energy)
    assert r.headers.get("X-CERTEUS-PCO-qlaw.tunneling.model_uri") == "lexqft://barrier/demo"
