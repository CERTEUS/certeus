#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/e2e/test_ui_pco_viewer.py                      |
# | ROLE: Minimal E2E: public PCO viewer path                     |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

from core.pco.crypto import (
    canonical_bundle_hash_hex,
    canonical_digest_hex,
    compute_leaf_hex,
    ed25519_sign_b64u,
)
from services.api_gateway.main import app


def _gen_ed25519_pair() -> tuple[bytes, bytes]:
    sk = Ed25519PrivateKey.generate()
    sk_raw = sk.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption(),
    )
    pk_raw = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)
    return sk_raw, pk_raw


def test_public_pco_viewer_roundtrip(tmp_path: Path, monkeypatch) -> None:
    # Arrange: generate keys in-env (public only is required by router)
    sk, pk = _gen_ed25519_pair()
    monkeypatch.setenv("ED25519_PUBKEY_HEX", pk.hex())

    # Minimal public bundle with empty merkle path (root==leaf)
    rid = "ci-viewer-1"
    smt2_hash = "d" * 64
    lfsc = "(check-sat)"  # placeholder LFSC text
    drat = None
    bundle_hash = canonical_bundle_hash_hex(smt2_hash, lfsc, drat)
    leaf = compute_leaf_hex(rid, bundle_hash)
    merkle_path: list[dict[str, str]] = []
    digest = canonical_digest_hex(
        rid=rid, smt2_hash_hex=smt2_hash, lfsc_text=lfsc, merkle_root_hex=leaf, drat_text=drat
    )
    signature = ed25519_sign_b64u(sk, digest)

    # Persist under data/public_pco (as expected by router)
    pub_dir = Path("data/public_pco")
    (tmp_path / pub_dir).mkdir(parents=True, exist_ok=True)
    # Point router to our tmp bundle dir explicitly
    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path / pub_dir))
    # Make cwd-relative path point to tmp (for any fallback uses)
    monkeypatch.chdir(tmp_path)
    body = {
        "rid": rid,
        "smt2_hash": smt2_hash,
        "lfsc": lfsc,
        "drat": drat,
        "merkle_proof": merkle_path,
        "signature": signature,
    }
    (tmp_path / pub_dir / f"{rid}.json").write_text(json.dumps(body), encoding="utf-8")

    # Act
    client = TestClient(app)
    r = client.get(f"/pco/public/{rid}")

    # Assert
    assert r.status_code == 200, r.text
    out = r.json()
    assert out["rid"] == rid
    assert out["smt2_hash"] == smt2_hash
    assert out["merkle_proof"] == []


def test_public_pco_viewer_merkle_step(tmp_path: Path, monkeypatch) -> None:
    sk, pk = _gen_ed25519_pair()
    monkeypatch.setenv("ED25519_PUBKEY_HEX", pk.hex())
    rid = "ci-merkle-1"
    smt2_hash = "a" * 64
    lfsc = "(check-sat)"
    drat = None
    bundle_hash = canonical_bundle_hash_hex(smt2_hash, lfsc, drat)
    leaf = compute_leaf_hex(rid, bundle_hash)
    # One-step path to the left: root = H(sib || leaf)
    sibling_hex = "b" * 64
    import hashlib

    root_bytes = hashlib.sha256(bytes.fromhex(sibling_hex) + bytes.fromhex(leaf)).digest()
    merkle_root = root_bytes.hex()
    merkle_path = [{"sibling": sibling_hex, "dir": "L"}]
    digest = canonical_digest_hex(
        rid=rid, smt2_hash_hex=smt2_hash, lfsc_text=lfsc, merkle_root_hex=merkle_root, drat_text=drat
    )
    signature = ed25519_sign_b64u(sk, digest)
    pub_dir = Path("data/public_pco")
    (tmp_path / pub_dir).mkdir(parents=True, exist_ok=True)
    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path / pub_dir))
    monkeypatch.chdir(tmp_path)
    body = {
        "rid": rid,
        "smt2_hash": smt2_hash,
        "lfsc": lfsc,
        "drat": drat,
        "merkle_proof": merkle_path,
        "signature": signature,
    }
    (tmp_path / pub_dir / f"{rid}.json").write_text(json.dumps(body), encoding="utf-8")
    client = TestClient(app)
    r = client.get(f"/pco/public/{rid}")
    assert r.status_code == 200, r.text
    out = r.json()
    assert out["rid"] == rid
    assert out["merkle_proof"][0]["dir"] == "L"
