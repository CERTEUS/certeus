#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_lexqft_renorm.py                |
# | ROLE: LexQFT renorm tests                                   |
# | PLIK: tests/services/test_lexqft_renorm.py                |
# | ROLA: Testy renormalizacji autorytetu                       |
# +-------------------------------------------------------------+
"""
PL: W4 — Renormalizacja autorytetu (cldf.renorm.*):
 - Normalizacja [2,3,5] → [0.2,0.3,0.5].
 - Suma = 1.0; przypadek suma 0 → rozkład jednostajny.
EN:
 - Normalization [2,3,5] → [0.2,0.3,0.5].
 - Sum = 1.0; zero-sum → uniform.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def _dist_to_map(dist):
    return {it["uid"]: float(it["p"]) for it in dist}


def test_renorm_basic_distribution_and_sum() -> None:
    r = client.post(
        "/v1/lexqft/renorm",
        json={
            "case": "R-1",
            "items": [
                {"uid": "A", "authority": 2.0},
                {"uid": "B", "authority": 3.0},
                {"uid": "C", "authority": 5.0},
            ],
        },
    )
    assert r.status_code == 200
    body = r.json()
    mp = _dist_to_map(body["dist"])
    assert abs(sum(mp.values()) - 1.0) < 1e-9
    assert abs(mp.get("A", 0.0) - 0.2) < 1e-9
    assert abs(mp.get("B", 0.0) - 0.3) < 1e-9
    assert abs(mp.get("C", 0.0) - 0.5) < 1e-9


def test_renorm_zero_sum_uniform() -> None:
    r = client.post(
        "/v1/lexqft/renorm",
        json={
            "items": [
                {"uid": "X", "authority": 0.0},
                {"uid": "Y", "authority": 0.0},
                {"uid": "Z", "authority": 0.0},
            ]
        },
    )
    assert r.status_code == 200
    body = r.json()
    mp = _dist_to_map(body["dist"])
    assert abs(sum(mp.values()) - 1.0) < 1e-9
    # All equal
    vals = list(mp.values())
    assert len(set(round(v, 9) for v in vals)) == 1
