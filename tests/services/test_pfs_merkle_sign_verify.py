#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_merkle_sign_verify.py       |
# | ROLE: PFS Merkle sign/verify tests                          |
# | PLIK: tests/services/test_pfs_merkle_sign_verify.py       |
# | ROLA: Testy podpisu/wer. Merkle ścieżek                     |
# +-------------------------------------------------------------+
"""
PL: W9 — PQ-crypto (stub: Ed25519) podpis merkle root ścieżki i weryfikacja.
EN: W9 — PQ-crypto stub: Ed25519 signing of merkle root and verification.
"""

from __future__ import annotations

import base64

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).decode("ascii").rstrip("=")


def test_merkle_sign_and_verify_roundtrip() -> None:
    sk = Ed25519PrivateKey.generate()
    pk = sk.public_key()
    sk_b = sk.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption(),
    )
    pk_b = pk.public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)

    path = ["lexqft.tunnel", "cfe.geodesic", "proofgate.publish"]

    r = client.post(
        "/v1/pfs/sign_path",
        json={"case": "MERKLE-1", "path": path, "sk_b64url": _b64u(sk_b)},
    )
    assert r.status_code == 200
    body = r.json()
    sig = body.get("signature_b64")
    assert isinstance(sig, str) and len(sig) > 0

    rv = client.post(
        "/v1/pfs/verify_path",
        json={
            "case": "MERKLE-1",
            "path": path,
            "pk_b64url": _b64u(pk_b),
            "signature_b64": sig,
        },
    )
    assert rv.status_code == 200 and rv.json().get("ok") is True
