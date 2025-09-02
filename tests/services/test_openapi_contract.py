from __future__ import annotations

from fastapi.testclient import TestClient


def test_openapi_contains_key_endpoints() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)
    r = c.get("/openapi.json")
    assert r.status_code == 200
    doc = r.json()
    paths = doc.get("paths", {})
    # A few representative endpoints across domains
    for p in [
        "/v1/qtm/measure",
        "/v1/lexqft/tunnel",
        "/v1/cfe/curvature",
        "/v1/devices/horizon_drive/plan",
        "/v1/pco/bundle",
        "/v1/ledger/{case_id}/records",
    ]:
        assert p in paths, f"missing {p} in OpenAPI"
