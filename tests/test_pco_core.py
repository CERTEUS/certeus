#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/test_pco_core.py                              |

# | ROLE: Project module.                                       |

# | PLIK: tests/test_pco_core.py                              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from hashlib import sha256

# ----Bloki----- IMPORTY
import time

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
import pytest

from core.pco import (
    PublicPCO,
    apply_merkle_path,
    canonical_bundle_hash_hex,
    canonical_digest_hex,
    compute_leaf_hex,
    ed25519_verify_b64u,
)


def _hex(s: str) -> str:
    return sha256(s.encode("utf-8")).hexdigest()


def test_kernel_bundle_hash_and_leaf() -> None:
    smt2_hash = _hex("(set-logic ALL)\n(check-sat)")

    lfsc = "(lfsc proof)"

    bundle_hash = canonical_bundle_hash_hex(smt2_hash, lfsc, None)

    leaf = compute_leaf_hex("demo-001", bundle_hash)

    # sanity: długości

    assert len(bundle_hash) == 64

    assert len(leaf) == 64


def test_kernel_canonical_digest_and_sig() -> None:
    sk = Ed25519PrivateKey.generate()

    pk = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)

    smt2_hash = _hex("(set-logic ALL)\n(check-sat)")

    lfsc = "(lfsc proof)"

    drat = None

    bundle_hash = canonical_bundle_hash_hex(smt2_hash, lfsc, drat)

    root = apply_merkle_path(compute_leaf_hex("demo-001", bundle_hash), [])  # MVP: []

    digest = canonical_digest_hex(
        rid="demo-001", smt2_hash_hex=smt2_hash, lfsc_text=lfsc, drat_text=drat, merkle_root_hex=root
    )

    sig = sk.sign(bytes.fromhex(digest))

    ed25519_verify_b64u(pk, __import__("base64").urlsafe_b64encode(sig).rstrip(b"=").decode(), digest)


def test_kernel_build_and_verify() -> None:
    sk = Ed25519PrivateKey.generate()

    pk = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)

    rid = "demo-001"

    smt2_hash = _hex("(set-logic ALL)\n(check-sat)")

    lfsc = "(lfsc proof)"

    # MVP: merkle_proof=[]

    pco = PublicPCO.build_and_sign(
        rid=rid,
        smt2_hash=smt2_hash,
        lfsc=lfsc,
        merkle_proof_raw=[],
        ed25519_private_bytes=sk.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),  # type: ignore[arg-type]
        ),  # raw bytes
        issued_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    )

    # verify

    pco.verify(ed25519_public_bytes=pk)

    # negatyw: zła sygnatura

    bad = PublicPCO(
        rid=rid,
        smt2_hash=smt2_hash,
        lfsc=lfsc,
        merkle_proof=[],
        signature="A" * 40,
        issued_at=None,
    )

    with pytest.raises(InvalidSignature):
        # verify should raise when signature invalid

        ed25519_verify_b64u(
            pk,
            bad.signature,
            canonical_digest_hex(
                rid=bad.rid,
                smt2_hash_hex=bad.smt2_hash,
                lfsc_text=bad.lfsc,
                drat_text=None,
                merkle_root_hex=compute_leaf_hex(bad.rid, canonical_bundle_hash_hex(bad.smt2_hash, bad.lfsc, None)),
            ),
        )
