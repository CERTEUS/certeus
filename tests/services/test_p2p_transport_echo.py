#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_p2p_transport_echo.py            |
# | ROLE: Enterprise test: P2P transport echo endpoint         |
# +-------------------------------------------------------------+

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_p2p_transport_echo_endpoint() -> None:
    c = TestClient(app)
    msg = "enterprise-check"
    r = c.get("/v1/p2p/transport/echo", params={"msg": msg})
    r.raise_for_status()
    body = r.json()
    assert body.get("ok") is True
    assert body.get("message") == msg
    assert isinstance(body.get("a"), str) and body.get("a").startswith("spiffe://")
    assert isinstance(body.get("b"), str) and body.get("b").startswith("spiffe://")
