#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_exists.py                     |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_pfs_exists.py                     |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Test HEAD/exists ProofFS (pfs:// URI) — pozytywny i negatywny przypadek.
EN: ProofFS exists (pfs:// URI) — positive and negative case.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import tempfile

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def test_pfs_exists_endpoint() -> None:
    client = TestClient(app)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        # point ProofFS root
        import os

        os.environ["PROOFS_FS_ROOT"] = str(root)
        # prepare file
        p = root / "mail" / "MID" / "file.txt"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("X", encoding="utf-8")
        # exists
        r1 = client.get("/v1/pfs/exists", params={"uri": "pfs://mail/MID/file.txt"})
        assert r1.status_code == 200 and r1.json().get("exists") is True
        # not exists
        r2 = client.get("/v1/pfs/exists", params={"uri": "pfs://mail/MID/missing.txt"})
        assert r2.status_code == 200 and r2.json().get("exists") is False

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
