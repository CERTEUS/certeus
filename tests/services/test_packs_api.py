#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_packs_api.py                     |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_packs_api.py                     |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Testy API paczek (Marketplace): listowanie i togglowanie enable/disable.
EN: Packs API (Marketplace) tests: listing and enable/disable toggling.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
import tempfile
from typing import Any

from fastapi.testclient import TestClient


def test_packs_list_and_toggle() -> None:
    # Skonfiguruj odseparowaną ścieżkę stanu, aby nie mieszać globalnego stanu
    with tempfile.TemporaryDirectory() as td:
        state_path = os.path.join(td, "packs_state.json")
        os.environ["PACKS_STATE_PATH"] = state_path

        from services.api_gateway.main import app

        c = TestClient(app)

        # Lista: musi być >= 1 pakiet
        r = c.get("/v1/packs/")
        assert r.status_code == 200
        items: list[dict[str, Any]] = r.json()
        assert isinstance(items, list) and len(items) >= 1
        name = str(items[0]["name"])  # dowolny pierwszy

        # Toggle → disable
        r2 = c.post("/v1/packs/enable", json={"pack": name, "enabled": False})
        assert r2.status_code == 200 and r2.json().get("ok") is True

        # Weryfikacja overlayu (enabled=False)
        r3 = c.get("/v1/packs/")
        assert r3.status_code == 200
        items2: list[dict[str, Any]] = r3.json()
        d = {i["name"]: i for i in items2}
        assert d[name]["enabled"] is False

        # Toggle → enable (powrót)
        r4 = c.post("/v1/packs/enable", json={"pack": name, "enabled": True})
        assert r4.status_code == 200 and r4.json().get("ok") is True

        # Sprawdź zapis pliku stanu
        with open(state_path, encoding="utf-8") as fh:
            js = json.load(fh)
        assert isinstance(js, dict) and name in js
