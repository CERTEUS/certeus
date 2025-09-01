#!/usr/bin/env python3

"""
PL: Public payload PCO: ekstrakcja i walidacja (bez PII).

EN: PCO public payload: extraction and validation (no PII).
"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/pco/public_payload.py                          |

# | ROLE: Project module.                                       |

# | PLIK: core/pco/public_payload.py                          |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

# ----Bloki----- IMPORTY
from dataclasses import asdict, dataclass
from typing import Any

from .crypto import (
    canonical_bundle_hash_hex,
    canonical_digest_hex,
    compute_leaf_hex,
    ed25519_sign_b64u,
    ed25519_verify_b64u,
)
from .merkle import MerkleStep, apply_merkle_path, parse_merkle_proof

# ----Bloki----- KONSTANTY

FORBIDDEN_KEYS: set[str] = {
    "name",
    "first_name",
    "last_name",
    "pesel",
    "email",
    "phone",
    "address",
    "dob",
    "ssn",
    "patient_id",
    "person_id",
    "user_id",
    "ip",
    "session_id",
    "headers",
}


# ----Bloki----- MODEL


@dataclass(slots=True)
class PublicPCO:
    rid: str

    smt2_hash: str

    lfsc: str

    merkle_proof: list[MerkleStep]

    signature: str

    drat: str | None = None

    issued_at: str | None = None  # informacyjne, niewchodzące do digestu

    # ----Bloki----- BUDOWA

    @staticmethod
    def build_and_sign(
        *,
        rid: str,
        smt2_hash: str,
        lfsc: str,
        merkle_proof_raw: Any,
        ed25519_private_bytes: bytes,
        drat: str | None = None,
        issued_at: str | None = None,
    ) -> PublicPCO:
        proof = parse_merkle_proof(merkle_proof_raw)

        bundle_hash = canonical_bundle_hash_hex(smt2_hash, lfsc, drat)

        merkle_root = (
            apply_merkle_path(compute_leaf_hex(rid, bundle_hash), proof)
            if proof
            else compute_leaf_hex(rid, bundle_hash)
        )

        digest = canonical_digest_hex(
            rid=rid,
            smt2_hash_hex=smt2_hash,
            lfsc_text=lfsc,
            drat_text=drat,
            merkle_root_hex=merkle_root,
        )

        sig = ed25519_sign_b64u(ed25519_private_bytes, digest)

        return PublicPCO(
            rid=rid,
            smt2_hash=smt2_hash.lower(),
            lfsc=lfsc,
            drat=drat,
            merkle_proof=proof,
            signature=sig,
            issued_at=issued_at,
        )

    # ----Bloki----- WERYFIKACJA

    def verify(self, *, ed25519_public_bytes: bytes) -> None:
        # 0 PII – kontrola kluczy nazewniczo (sam payload ma tylko pola dozwolone)

        forbidden = sorted(set(asdict(self).keys()) & FORBIDDEN_KEYS)

        if forbidden:
            raise ValueError(f"PII field(s) present: {forbidden}")

        bundle_hash = canonical_bundle_hash_hex(self.smt2_hash, self.lfsc, self.drat)

        leaf = compute_leaf_hex(self.rid, bundle_hash)

        root = apply_merkle_path(leaf, self.merkle_proof) if self.merkle_proof else leaf

        digest = canonical_digest_hex(
            rid=self.rid,
            smt2_hash_hex=self.smt2_hash,
            lfsc_text=self.lfsc,
            drat_text=self.drat,
            merkle_root_hex=root,
        )

        ed25519_verify_b64u(ed25519_public_bytes, self.signature, digest)
