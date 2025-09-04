#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_fin_paper.py                     |
# | ROLE: Paper trading sandbox tests (FIN)                      |
# | PLIK: tests/services/test_fin_paper.py                     |
# | ROLA: Testy sandboxa "paper trading" (FIN)                   |
# +-------------------------------------------------------------+

"""
PL: Minimalne testy W5 — otwarcie konta, złożenie zlecenia i odczyt pozycji.

EN: Minimal W5 tests — open account, place order, and read positions.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi.testclient import TestClient


def test_fin_paper_open_order_and_positions() -> None:
    from services.api_gateway.main import app

    c = TestClient(app)

    # Open account
    r = c.post("/v1/fin/alpha/paper/open", json={"capital": 1000.0})
    assert r.status_code == 200 and r.json().get("ok")

    # Place BUY 1 @ 100
    r = c.post(
        "/v1/fin/alpha/paper/order",
        json={"side": "BUY", "qty": 1.0, "price": 100.0, "symbol": "TEST"},
    )
    assert r.status_code == 200 and r.json().get("ok")

    # Positions
    r = c.get("/v1/fin/alpha/paper/positions")
    assert r.status_code == 200
    js = r.json()
    assert js.get("position") >= 1.0 - 1e-9
    assert js.get("cash") <= 1000.0 + 1e-9

    # Equity series
    r = c.get("/v1/fin/alpha/paper/equity")
    assert r.status_code == 200
    s = r.json().get("series")
    assert isinstance(s, list)
