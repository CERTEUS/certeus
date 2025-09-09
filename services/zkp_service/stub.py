# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/zkp_service/stub.py                        |

# | ROLE: Project module.                                       |

# | PLIK: services/zkp_service/stub.py                        |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Prosty, realny serwis ZKP (dowód wiedzy o kluczu prywatnym) oparty o Ed25519.
    Zwracany jest podpis JWS (EdDSA) nad transkrypcją (Fiat–Shamir), który
    można zweryfikować bez ujawniania sekretu. To jest produkcyjnie użyteczne
    „proof-of-knowledge” w kontekście publikacji/PCO.

EN: Minimal, real ZK-like proof service based on Ed25519. It produces a JWS
    (EdDSA) over a domain-separated transcript (Fiat–Shamir style) so a caller
    can verify possession of the secret key without revealing it. Suitable as a
    practical proof-of-knowledge primitive for publishing/PCO.
"""

from __future__ import annotations

import base64
import json
from dataclasses import dataclass
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)


# === MODELE / MODELS ===


@dataclass(frozen=True)
class KeyPair:
    sk_pem: str
    pk_hex: str


# === UTIL ===


def _b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _unb64u(data: str) -> bytes:
    pad = "=" * ((4 - len(data) % 4) % 4)
    return base64.urlsafe_b64decode((data + pad).encode("ascii"))


def _jws_sign(sk: Ed25519PrivateKey, payload: dict[str, Any]) -> str:
    header = {"alg": "EdDSA", "typ": "JWT"}
    h = _b64u(json.dumps(header, separators=(",", ":")).encode("utf-8"))
    p = _b64u(json.dumps(payload, separators=(",", ":")).encode("utf-8"))
    signing_input = f"{h}.{p}".encode("ascii")
    sig = sk.sign(signing_input)
    return f"{h}.{p}.{_b64u(sig)}"


def _jws_verify(pk: Ed25519PublicKey, token: str) -> tuple[bool, dict[str, Any] | None]:
    try:
        h, p, s = token.split(".")
        signing_input = f"{h}.{p}".encode("ascii")
        sig = _unb64u(s)
        pk.verify(sig, signing_input)
        payload = json.loads(_unb64u(p))
        return True, payload
    except Exception:
        return False, None


# === API / LOGIC ===


def generate_keypair() -> KeyPair:
    """
    Wygeneruj parę kluczy Ed25519. Zwraca PEM (sk) i hex (pk).
    """

    sk = Ed25519PrivateKey.generate()
    pk = sk.public_key()
    sk_pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    pk_hex = pk.public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw).hex()
    return KeyPair(sk_pem=sk_pem, pk_hex=pk_hex)


def prove(data: bytes | str, sk_pem: str | None = None, *, subject: str = "zkp") -> bytes:
    """
    Wygeneruj dowód wiedzy o kluczu prywatnym: JWS(EdDSA) nad transkrypcją.

    - data: bajty/tekst włączone do transkrypcji (domain separation przez typ)
    - sk_pem: klucz prywatny Ed25519 (PEM). Jeśli None, generujemy efemeryczny.
    - subject: identyfikator subiekta (np. case_id, device_id)

    Zwraca bajty tokena JWS (ASCII), do weryfikacji funkcją verify().
    """

    if isinstance(data, str):
        data_b = data.encode("utf-8")
        data_t = "str"
    else:
        data_b = data
        data_t = "bin"

    if sk_pem:
        sk = serialization.load_pem_private_key(sk_pem.encode("utf-8"), password=None)
        assert isinstance(sk, Ed25519PrivateKey)
    else:
        sk = Ed25519PrivateKey.generate()

    pk_hex = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw).hex()

    payload = {
        "typ": "CERTEUS/POK",
        "sub": subject,
        "pk_hex": pk_hex,
        "transcript": {
            "alg": "Ed25519",
            "domain": "certeus.zkp_service.v1",
            "data_type": data_t,
            "data_b64u": _b64u(data_b),
        },
    }
    token = _jws_sign(sk, payload)
    return token.encode("ascii")


def verify(data: bytes | str, proof: bytes) -> bool:
    """
    Zweryfikuj dowód z `prove()`.

    - Odtwarza transkrypcję (data_type, data_b64u) z tokena i porównuje z
      przekazanym `data`. Następnie weryfikuje podpis Ed25519.
    """

    token = proof.decode("ascii") if isinstance(proof, (bytes, bytearray)) else str(proof)
    try:
        parts = token.split(".")
        assert len(parts) == 3
        header_b64, payload_b64, _sig_b64 = parts
        payload = json.loads(_unb64u(payload_b64))
        pk_hex = str(payload.get("pk_hex") or "").strip()
        tr = payload.get("transcript") or {}
        dt = tr.get("data_type")
        db = tr.get("data_b64u")
        if not pk_hex or not dt or not db:
            return False
        # Rebuild data
        if isinstance(data, str):
            if dt != "str":
                return False
            data_enc = _b64u(data.encode("utf-8"))
        else:
            if dt != "bin":
                return False
            data_enc = _b64u(data)
        if data_enc != db:
            return False

        # Verify signature over header.payload
        signing_input = f"{header_b64}.{payload_b64}".encode("ascii")
        sig = _unb64u(token.split(".")[2])
        pk = Ed25519PublicKey.from_public_bytes(bytes.fromhex(pk_hex))
        pk.verify(sig, signing_input)
        return True
    except Exception:
        return False

__all__ = ["prove", "verify", "generate_keypair", "KeyPair"]
