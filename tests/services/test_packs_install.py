#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_packs_install.py                  |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_packs_install.py                  |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy instalacji/upgrade paczek (Marketplace) z podpisem.
EN: Tests for pack install/upgrade (Marketplace) with signature.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
import tempfile
from typing import Any

from fastapi.testclient import TestClient


def test_packs_install_with_signature_and_state() -> None:
    # Użyj odseparowanej ścieżki stanu
    with tempfile.TemporaryDirectory() as td:
        state_path = os.path.join(td, "packs_state.json")
        os.environ["PACKS_STATE_PATH"] = state_path

        from services.api_gateway.main import app

        c = TestClient(app)

        # Pobierz listę i wybierz paczkę
        r = c.get("/v1/packs/")
        assert r.status_code == 200
        items: list[dict[str, Any]] = r.json()
        assert items, "Brak paczek w Marketplace"
        name = str(items[0]["name"])  # dowolny

        # Instalacja z podpisem (64 hex — minimalny stub)
        sig = "a" * 64
        r2 = c.post(
            "/v1/packs/install",
            json={
                "pack": name,
                "signature": sig,
                "version": items[0].get("version") or "0.1.0",
            },
        )
        assert r2.status_code == 200
        body = r2.json()
        assert body.get("ok") is True and body.get("signature") is True

        # Weryfikacja stanu: obecny rekord z podpisem
        with open(state_path, encoding="utf-8") as fh:
            js = json.load(fh)
        assert isinstance(js, dict) and name in js
        entry = js[name]
        assert isinstance(entry, dict) and isinstance(entry.get("signature"), str)

        # Zły podpis — zbyt krótki
        r3 = c.post("/v1/packs/install", json={"pack": name, "signature": "short"})
        assert r3.status_code == 400

        # Lista odzwierciedla signature oraz installed_version
        r4 = c.get("/v1/packs/")
        assert r4.status_code == 200
        items2: list[dict[str, Any]] = r4.json()
        rec = {i["name"]: i for i in items2}[name]
        assert rec.get("signature") is True
        assert rec.get("installed_version") == (items[0].get("version") or "0.1.0")
