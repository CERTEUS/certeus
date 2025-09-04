#!/usr/bin/env python3
"""
PL: W15 — Idempotencja urządzeń: ta sama Idempotency-Key zwraca ten sam wynik bez podwójnego kosztu.
EN: W15 — Devices idempotency: same Idempotency-Key returns same result without double-charging.
"""

from __future__ import annotations

from fastapi.testclient import TestClient


def test_qoracle_idempotency_and_budget_once() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    tenant = "idem-tenant"
    # set quota to known value
    r = c.post("/v1/billing/quota", json={"tenant": tenant, "units": 10})
    assert r.status_code == 200
    # first call with key
    h = {"Idempotency-Key": "k-qo-1", "X-Tenant-ID": tenant}
    r1 = c.post("/v1/devices/qoracle/expectation", json={"question": "retry-safe"}, headers=h)
    assert r1.status_code == 200
    s1 = r1.headers.get("X-Idempotency-Status")
    # second call same key
    r2 = c.post("/v1/devices/qoracle/expectation", json={"question": "retry-safe"}, headers=h)
    assert r2.status_code == 200
    assert r1.json() == r2.json()
    s2 = r2.headers.get("X-Idempotency-Status")
    assert s1 == "new" and s2 == "reused"
    # verify budget deducted only once (endpoint cost is 2 units)
    rb = c.get("/v1/billing/balance", headers={"X-Tenant-ID": tenant})
    assert rb.status_code == 200
    bal = int(rb.json().get("balance"))
    assert bal == 8
