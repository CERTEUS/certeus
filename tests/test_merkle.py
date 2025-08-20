from __future__ import annotations

from hashlib import sha256

from services.ledger_service.cosmic_merkle import anchor_bundle, get_bundle_proof, verify_proof


def _hx(s: str) -> str:
    return sha256(s.encode("utf-8")).hexdigest()


def test_anchor_and_verify_roundtrip() -> None:
    rid = _hx("rid-1")
    bundle = _hx("bundle-1")

    receipt = anchor_bundle(rid, bundle)
    again = get_bundle_proof(rid, bundle)
    assert again is not None
    assert receipt.root == again.root
    assert verify_proof(receipt)
    assert verify_proof(again)
