#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/test_pco_public.py                            |

# | ROLE: Project module.                                       |

# | PLIK: tests/test_pco_public.py                            |

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

# stdlib
import base64
from hashlib import sha256
import json
from pathlib import Path
import time

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

# third-party
import pytest

# project
from services.api_gateway.main import app
from services.api_gateway.routers.pco_public import (  # type: ignore
    _canonical_digest_hex,
    compute_leaf_hex,
)

client = TestClient(app)

# ---Bloki----- POMOCNICZE

def _b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")

def _hex(s: str) -> str:
    return sha256(s.encode("utf-8")).hexdigest()

def _bundle_hash_hex(smt2_hash: str, lfsc_text: str, drat_text: str | None = None) -> str:
    """Musi odzwierciedlać serwerowe _compute_bundle_hash_hex."""

    payload = {"lfsc_sha256": _hex(lfsc_text), "smt2_hash": smt2_hash}

    if drat_text is not None:
        payload["drat_sha256"] = _hex(drat_text)

    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")

    return sha256(blob).hexdigest()

# ---Bloki----- TESTY

def test_get_public_pco_happy_path(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # GIVEN: środowisko i klucz testowy

    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path))

    sk = Ed25519PrivateKey.generate()

    pk_bytes = sk.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )

    monkeypatch.setenv("ED25519_PUBKEY_HEX", pk_bytes.hex())

    # AND: przygotowany publiczny bundle (MVP, path=[])

    rid = "demo-001"

    smt2_hash = _hex("(set-logic ALL)\n(check-sat)\n")

    lfsc = "(lfsc proof placeholder)"

    pub = {
        "rid": rid,
        "smt2_hash": smt2_hash,
        "lfsc": lfsc,
        # brak 'drat' (optional) w tym teście
        "merkle_proof": [],  # MVP: root==leaf
        "issued_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }

    # Oblicz bundle_hash -> liść Merkle -> digest kanoniczny i podpisz

    bundle_hash = _bundle_hash_hex(smt2_hash, lfsc)

    merkle_root = compute_leaf_hex(rid, bundle_hash)  # path == [] ⇒ root == leaf

    digest_hex = _canonical_digest_hex(pub, merkle_root)

    pub["signature"] = _b64u(sk.sign(bytes.fromhex(digest_hex)))

    # Zapisz bundle na FS

    (tmp_path / f"{rid}.json").write_text(json.dumps(pub, ensure_ascii=False), encoding="utf-8")

    # WHEN: pobieramy publiczny PCO

    r = client.get(f"/pco/public/{rid}")

    assert r.status_code == 200, r.text

    body = r.json()

    # THEN: sanity

    assert body["rid"] == rid

    assert "lfsc" in body

    assert "signature" in body

def test_get_public_pco_validation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path))

    rid = _hex("rid-bad")

    # Błędny JSON (tablica zamiast obiektu)

    (tmp_path / f"{rid}.json").write_text("[]", encoding="utf-8")

    r = client.get(f"/pco/public/{rid}")

    assert r.status_code in (400, 422, 500)
