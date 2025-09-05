#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_list_and_materialize.py       |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_pfs_list_and_materialize.py       |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Testy listowania ProofFS i materializacji załączników w MailOps (stub/dev).
EN: Tests for ProofFS listing and MailOps attachment materialization (stub/dev).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_pfs_list_returns_entries(monkeypatch) -> None:
    client = TestClient(app)
    with client:
        with os.scandir('.'):
            pass
    # Use temp directory under tests runtime for ProofFS root
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        # point ProofFS root to tmp
        monkeypatch.setenv("PROOFS_FS_ROOT", str(root))
        # create two files under mail/MID
        (root / "mail" / "MID").mkdir(parents=True, exist_ok=True)
        (root / "mail" / "MID" / "a.txt").write_text("A", encoding="utf-8")
        (root / "mail" / "MID" / "b.txt").write_text("B", encoding="utf-8")

        r = client.get("/v1/pfs/list", params={"prefix": "pfs://mail/MID"})
        assert r.status_code == 200
        data = r.json()
        uris = {e["uri"] for e in data.get("entries", [])}
        assert "pfs://mail/MID/a.txt" in uris
        assert "pfs://mail/MID/b.txt" in uris

        # recursive + mime filter
        (root / "mail" / "MID" / "sub").mkdir(parents=True, exist_ok=True)
        (root / "mail" / "MID" / "sub" / "c.pdf").write_text("C", encoding="utf-8")
        r2 = client.get(
            "/v1/pfs/list",
            params={"prefix": "pfs://mail/MID", "recursive": True, "mime": "pdf"},
        )
        assert r2.status_code == 200
        uris2 = {e["uri"] for e in r2.json().get("entries", [])}
        assert "pfs://mail/MID/sub/c.pdf" in uris2 and "pfs://mail/MID/a.txt" not in uris2


def test_mailops_ingest_materializes_when_flag(monkeypatch) -> None:
    client = TestClient(app)
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        monkeypatch.setenv("PROOFS_FS_ROOT", str(root))
        monkeypatch.setenv("PROOFS_FS_MATERIALIZE", "1")

        payload = {
            "mail_id": "MID-X",
            "from_addr": "a@example.com",
            "to": ["b@example.com"],
            "attachments": [{"filename": "x.pdf", "content_type": "application/pdf", "size": 1}],
        }
        r = client.post("/v1/mailops/ingest", json=payload)
        assert r.status_code == 200
        # file should exist
        p = root / "mail" / "MID-X" / "x.pdf"
        assert p.exists() and p.is_file()
