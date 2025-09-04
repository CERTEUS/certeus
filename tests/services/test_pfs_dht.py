#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_dht.py                      |
# | ROLE: ProofFS DHT tests                                      |
# | PLIK: tests/services/test_pfs_dht.py                      |
# | ROLA: Testy DHT kompetencji                                  |
# +-------------------------------------------------------------+
"""
PL: W8 — DHT kompetencji: announce/query/publish_path.
EN: Competency DHT.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_announce_and_query_and_publish() -> None:
    # Announce
    a1 = client.post(
        "/v1/pfs/dht/announce",
        json={"node": "node-A", "competencies": ["lexqft.*", "proof.*"], "capacity": 2},
    )
    assert a1.status_code == 200
    a2 = client.post(
        "/v1/pfs/dht/announce",
        json={"node": "node-B", "competencies": ["cfe.geodesic", "lexenith.*"], "capacity": 1},
    )
    assert a2.status_code == 200

    # Query
    q1 = client.get("/v1/pfs/dht/query", params={"competency": "lexqft.tunnel"}).json()
    assert "node-A" in q1.get("nodes", [])
    q2 = client.get("/v1/pfs/dht/query", params={"competency": "cfe.geodesic"}).json()
    assert "node-B" in q2.get("nodes", [])

    # Publish path
    pub = client.post(
        "/v1/pfs/dht/publish_path",
        json={"case": "DHT-1", "path": ["lexqft.tunnel", "cfe.geodesic", "proof.publish"]},
    )
    assert pub.status_code == 200
    body = pub.json()
    nodes = body.get("nodes") or []
    assert set(nodes).issubset({"node-A", "node-B"}) and len(nodes) >= 1
