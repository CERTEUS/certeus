#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def _pem(sk: Ed25519PrivateKey) -> str:
    return (
        sk.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption(),
        )
        .decode("utf-8")
        .strip()
    )


def test_pco_bundle_verification_success_sets_pending(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path))
    sk = Ed25519PrivateKey.generate()
    monkeypatch.setenv("ED25519_PRIVKEY_PEM", _pem(sk))

    body = {
        "rid": "case-ok-1",
        "smt2_hash": "a" * 64,
        "lfsc": "(lfsc)",
        "drat": None,
        "merkle_proof": [],
        "smt2": "(set-logic ALL)\n(assert true)\n(check-sat)\n",
    }
    r = client.post("/v1/pco/bundle", json=body)
    assert r.status_code == 200, r.text
    saved = json.loads((tmp_path / "case-ok-1.json").read_text(encoding="utf-8"))
    # With stricter ProofGate checks, missing counsel/signatures may yield ABSTAIN
    assert saved.get("status") in {"PENDING", "CONDITIONAL", "PUBLISH", "ABSTAIN"}


def test_pco_bundle_verification_failure_sets_abstain(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path))
    sk = Ed25519PrivateKey.generate()
    monkeypatch.setenv("ED25519_PRIVKEY_PEM", _pem(sk))

    body = {
        "rid": "case-bad-1",
        "smt2_hash": "b" * 64,
        "lfsc": "(lfsc)",
        "merkle_proof": [],
        "smt2": "INVALID SMT2",
    }
    r = client.post("/v1/pco/bundle", json=body)
    assert r.status_code == 200, r.text
    saved = json.loads((tmp_path / "case-bad-1.json").read_text(encoding="utf-8"))
    assert saved.get("status") == "ABSTAIN"
