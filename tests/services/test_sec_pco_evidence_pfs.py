#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_sec_pco_evidence_pfs.py          |
# | ROLE: Project test module.                                  |
# | PLIK: tests/services/test_sec_pco_evidence_pfs.py          |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Smoke: URI z `security.evidence[].uri` wskazuje na istniejący artefakt ProofFS.
EN: Smoke: URIs from `security.evidence[].uri` point to existing ProofFS artifacts.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import tempfile

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_sec_pco_evidence_pfs_exists() -> None:
    client = TestClient(app)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        # point ProofFS root
        import os

        os.environ["PROOFS_FS_ROOT"] = str(root)
        # prepare an evidence file under pfs://mail/MSEC/rep.pdf
        p = root / "mail" / "MSEC" / "rep.pdf"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("SEC-EVIDENCE", encoding="utf-8")

        # SEC-PO-like evidence URI
        evidence_uri = "pfs://mail/MSEC/rep.pdf"

        r = client.get("/v1/pfs/exists", params={"uri": evidence_uri})
        assert r.status_code == 200 and r.json().get("exists") is True

        # negative
        r2 = client.get("/v1/pfs/exists", params={"uri": "pfs://mail/MSEC/missing.pdf"})
        assert r2.status_code == 200 and r2.json().get("exists") is False
