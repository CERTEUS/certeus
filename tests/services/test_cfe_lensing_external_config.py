#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_cfe_lensing_external_config.py   |
# | ROLE: Test module.                                          |
# | PLIK: tests/services/test_cfe_lensing_external_config.py   |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Test zewnętrznej konfiguracji lensingu CFE (JSON + ENV override).

EN: Test external JSON configuration for CFE lensing (ENV override).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path

from fastapi.testclient import TestClient


def test_external_lensing_config_via_env(tmp_path: Path, monkeypatch) -> None:
    from services.api_gateway.main import app

    # Prepare external config file
    cfg = {
        "lensing": {"MED": {"custom:MEDKEY": 0.55}},
        "lock": {"domains": ["MED", "SEC"], "severities": ["high", "critical"]},
    }
    cfg_path = tmp_path / "cfe_lensing.json"
    cfg_path.write_text(json.dumps(cfg, ensure_ascii=False), encoding="utf-8")

    # Point loader to external file
    monkeypatch.setenv("CERTEUS_CFE_LENSING_CONFIG", str(cfg_path))

    c = TestClient(app)
    r = c.get("/v1/cfe/lensing?domain=MED")
    assert r.status_code == 200
    lm = r.json().get("lensing_map", {})
    # Custom key from external config should be present
    assert "custom:MEDKEY" in lm
    assert 0.0 <= float(lm["custom:MEDKEY"]) <= 1.0


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
