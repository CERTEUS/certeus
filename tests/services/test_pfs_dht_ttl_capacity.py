#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_dht_ttl_capacity.py         |
# | ROLE: DHT TTL/capacity tests                                 |
# | PLIK: tests/services/test_pfs_dht_ttl_capacity.py         |
# | ROLA: Testy TTL/pojemności DHT                               |
# +-------------------------------------------------------------+

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_dht_ttl_and_capacity_assignment() -> None:
    # Expired node (ttl=0) should not match
    client.post(
        "/v1/pfs/dht/announce",
        json={
            "node": "node-expired",
            "competencies": ["lexqft.*"],
            "capacity": 10,
            "ttl_sec": 0,
        },
    )
    q = client.get("/v1/pfs/dht/query", params={"competency": "lexqft.tunnel"}).json()
    assert "node-expired" not in q.get("nodes", [])

    # Two nodes: capacity 1 vs 3; assign 4 steps → prefer higher capacity
    client.post(
        "/v1/pfs/dht/announce",
        json={
            "node": "node-low",
            "competencies": ["proof.*"],
            "capacity": 1,
            "ttl_sec": 3600,
        },
    )
    client.post(
        "/v1/pfs/dht/announce",
        json={
            "node": "node-high",
            "competencies": ["proof.*"],
            "capacity": 3,
            "ttl_sec": 3600,
        },
    )
    pub = client.post(
        "/v1/pfs/dht/publish_path",
        json={
            "case": "DHT-CAP",
            "path": [
                "proof.publish",
                "proof.publish",
                "proof.publish",
                "proof.publish",
            ],
        },
    )
    assert pub.status_code == 200
    body = pub.json()
    assigned = body.get("assigned", {})
    # node-high should get at least as many as node-low; ideally more
    assert int(assigned.get("node-high", 0)) >= int(assigned.get("node-low", 0))
