#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_dispute.py               |
# | ROLE: Dispute profile tests for WKB                         |
# | PLIK: tests/services/test_lexqft_dispute.py               |
# | ROLA: Testy profili spornych tunelowania                    |
# +-------------------------------------------------------------+
"""
PL: W6 — Scenariusze sporów: authority_bias vs evidence_bias vs balanced.
EN: Dispute scenarios.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def _pt(e: float, V0: float, w: float, profile: str | None):
    body = {"evidence_energy": e, "barrier_model": {"V0": V0, "w": w, "m": 1.0}}
    if profile:
        body["dispute_profile"] = profile
    r = client.post("/v1/lexqft/tunnel", json=body)
    assert r.status_code == 200
    return float(r.json()["p_tunnel"])


def test_dispute_profiles_ordering() -> None:
    # Typical disputed case: E<V0
    E, V0, w = 0.6, 1.0, 1.5
    p_auth = _pt(E, V0, w, "authority_bias")
    p_bal = _pt(E, V0, w, "balanced")
    p_evid = _pt(E, V0, w, "evidence_bias")
    assert p_auth < p_bal < p_evid


def test_asymmetric_profile_reduces_p_when_below_barrier() -> None:
    E, V0, w = 0.4, 1.0, 1.2
    p_asym = _pt(E, V0, w, "asymmetric")
    p_bal = _pt(E, V0, w, "balanced")
    assert p_asym <= p_bal
