#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_qtm_preset.py                   |
# | ROLE: Project module.                                       |
# | PLIK: tests/services/test_qtm_preset.py                   |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Testy API presetów Operator Composer: zapis/odczyt/lista.
EN: Tests for Operator Composer presets API: save/get/list.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===
from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

client = TestClient(app)


# === I/O / ENDPOINTS ===


# === TESTY / TESTS ===


def test_qtm_preset_save_get_list_roundtrip() -> None:
    case_id = "LEX-TEST-PRESET"
    op = "T"
    r = client.post("/v1/qtm/preset", json={"case": case_id, "operator": op})
    assert r.status_code == 200
    body = r.json()
    assert body["case"] == case_id and body["operator"] == op

    r2 = client.get(f"/v1/qtm/preset/{case_id}")
    assert r2.status_code == 200
    assert r2.json()["operator"] == op

    r3 = client.get("/v1/qtm/presets")
    assert r3.status_code == 200
    arr = r3.json()
    assert any(it["case"] == case_id and it["operator"] == op for it in arr)
