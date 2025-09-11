#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/test_zkp_service.py                             |
# | ROLE: Unit tests for ZKP service                            |
# +-------------------------------------------------------------+

from __future__ import annotations

from certeus.services.zkp_service import stub as zkp


def test_prove_and_verify_roundtrip_str() -> None:
    kp = zkp.generate_keypair()
    msg = "hello-certeus"
    proof = zkp.prove(msg, sk_pem=kp.sk_pem, subject="ut")
    assert isinstance(proof, (bytes, bytearray))
    assert zkp.verify(msg, proof) is True


def test_verify_rejects_tampered_data() -> None:
    kp = zkp.generate_keypair()
    data = b"payload-bin-01"
    ok = zkp.prove(data, sk_pem=kp.sk_pem)
    assert zkp.verify(data, ok) is True
    assert zkp.verify(b"different", ok) is False


def test_verify_rejects_corrupted_token() -> None:
    kp = zkp.generate_keypair()
    data = "abc"
    proof = zkp.prove(data, sk_pem=kp.sk_pem)
    bad = proof[:-2] + b"xx"
    assert zkp.verify(data, bad) is False

