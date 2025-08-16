# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |      Core Engine for Reliable & Unified Systems             |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_sipp.py                           |
# | ROLE: Integration tests for SIPP Indexer endpoint.          |
# +-------------------------------------------------------------+

"""
PL: Testuje endpoint /v1/sipp/snapshot/{act_id}.
EN: Tests the /v1/sipp/snapshot/{act_id} endpoint.
"""

from __future__ import annotations

from fastapi.testclient import TestClient
from services.api_gateway.main import app


client = TestClient(app)


def test_get_snapshot_endpoint_success() -> None:
    # Arrange
    act_id = "kk-art-286"

    # Act
    resp = client.get(f"/v1/sipp/snapshot/{act_id}")

    # Assert
    assert resp.status_code == 200
    data = resp.json()
    assert data["act_id"] == act_id
    assert data["version_id"] == "2023-10-01"
    assert data["source_url"]
    assert data["text_sha256"].startswith("sha256:")
    assert "snapshot_timestamp" in data
