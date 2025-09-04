#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_inspect.py                   |
# | ROLE: PFS inspector tests                                    |
# | PLIK: tests/services/test_pfs_inspect.py                   |
# | ROLA: Testy inspektora PFS                                   |
# +-------------------------------------------------------------+

"""
PL: Spina LEX Why‑Not z PFS inspect — URI pfs://why-not/<hash> powinien
    przejść inspekcję i zwrócić kind=why-not oraz ten sam hash.

EN: Connects LEX Why‑Not to PFS inspect — pfs://why-not/<hash> must inspect
    with kind=why-not and the same hash.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_pfs_inspect_why_not_uri() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    # First obtain a pfs://why-not/<hash> from LEX endpoint
    r = c.post("/v1/lexenith/why_not/export", json={"claim": "X", "counter_arguments": ["Y"]})
    assert r.status_code == 200
    uri = r.json().get("trace_uri")
    assert isinstance(uri, str) and uri.startswith("pfs://why-not/")
    hash_tail = uri.rsplit("/", 1)[-1]

    # Inspect via PFS endpoint
    r = c.get("/v1/pfs/inspect", params={"uri": uri})
    assert r.status_code == 200
    js = r.json()
    assert js.get("kind") == "why-not"
    assert js.get("hash") == hash_tail
