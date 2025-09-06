#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_renorm_properties.py     |
# | ROLE: Property tests for renorm                             |
# | PLIK: tests/services/test_lexqft_renorm_properties.py     |
# | ROLA: Testy własności renormalizacji                        |
# +-------------------------------------------------------------+
"""
PL: Agresywne własności dla renorm:
 - Skala: mnożenie autorytetów przez stałą nie zmienia rozkładu.
 - Suma 1 i brak wartości ujemnych.
 - Entropia w [0, ln(n)].
"""

from __future__ import annotations

import math

from fastapi.testclient import TestClient
from hypothesis import given, settings, strategies as st

from services.api_gateway.main import app

client = TestClient(app)


def _renorm(items, case: str = "HP-RENORM"):
    r = client.post("/v1/lexqft/renorm", json={"case": case, "items": items})
    assert r.status_code == 200
    body = r.json()
    dist = {d["uid"]: float(d["p"]) for d in body["dist"]}
    return dist, float(body.get("entropy", 0.0))


@given(
    xs=st.lists(
        st.floats(
            min_value=0.0, max_value=100.0, allow_nan=False, allow_infinity=False
        ),
        min_size=2,
        max_size=8,
    ),
    scale=st.floats(
        min_value=0.1, max_value=10.0, allow_nan=False, allow_infinity=False
    ),
)
@settings(deadline=None, max_examples=50)
def test_scale_invariance_and_entropy_bounds(xs, scale) -> None:
    items = [{"uid": f"U{i}", "authority": float(x)} for i, x in enumerate(xs)]
    dist, ent = _renorm(items, case="HP-RENORM-1")
    n = len(dist)
    s = sum(dist.values())
    assert abs(s - 1.0) < 1e-9
    assert all(p >= 0.0 for p in dist.values())
    assert 0.0 <= ent <= math.log(max(1, n)) + 1e-9

    # scale invariance
    items2 = [
        {"uid": f"U{i}", "authority": float(x) * float(scale)} for i, x in enumerate(xs)
    ]
    dist2, ent2 = _renorm(items2, case="HP-RENORM-2")
    for k in dist:
        assert abs(dist2[k] - dist[k]) < 1e-9
    # entropy equal as distributions equal
    assert abs(ent2 - ent) < 1e-9
