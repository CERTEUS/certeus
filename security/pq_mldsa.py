#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: security/pq_mldsa.py                                 |
# | ROLE: ML-DSA (Dilithium) adapter (optional, via pyoqs)     |
# | PLIK: security/pq_mldsa.py                                 |
# | ROLA: Adapter ML-DSA (Dilithium) (opcjonalnie, pyoqs)      |
# +-------------------------------------------------------------+

"""
PL: Adapter kryptografii post‑kwantowej (ML‑DSA/Dilithium) z użyciem biblioteki
    pyoqs (jeśli dostępna). Interfejs: generate_keypair(), sign(), verify().

EN: Post‑quantum crypto adapter (ML‑DSA/Dilithium) using pyoqs if available.
    Interface: generate_keypair(), sign(), verify().

Bez zależności twardych: importy wykonywane leniwie; brak pyoqs ⇒ ImportError.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple


def _oqs():  # lazy import to avoid hard dependency in CI
    try:
        import oqs  # type: ignore

        return oqs
    except Exception as e:  # pragma: no cover - environment dependent
        raise ImportError("pyoqs (oqs) not available: install 'oqs' package") from e


ALG = "Dilithium3"


@dataclass(frozen=True)
class MLDSAKeypair:
    public_key: bytes
    secret_key: bytes
    alg: str = ALG


def generate_keypair(alg: str = ALG) -> MLDSAKeypair:
    oqs = _oqs()
    with oqs.Signature(alg) as signer:
        pk = signer.generate_keypair()
        sk = signer.export_secret_key()
    return MLDSAKeypair(public_key=pk, secret_key=sk, alg=alg)


def sign(message: bytes, sk: bytes, alg: str = ALG) -> bytes:
    oqs = _oqs()
    with oqs.Signature(alg, secret_key=sk) as signer:
        return signer.sign(message)


def verify(message: bytes, signature: bytes, pk: bytes, alg: str = ALG) -> bool:
    oqs = _oqs()
    with oqs.Signature(alg) as verifier:
        try:
            return verifier.verify(message, signature, pk)
        except Exception:
            return False


__all__ = [
    "MLDSAKeypair",
    "generate_keypair",
    "sign",
    "verify",
]

