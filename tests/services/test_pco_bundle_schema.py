#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_pco_bundle_schema.py            |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_pco_bundle_schema.py            |

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

import base64
import json
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient
from jsonschema import Draft202012Validator

from services.api_gateway.main import app

client = TestClient(app)

def _b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")

def test_post_pco_bundle_builds_valid_proofbundle(tmp_path: Path, monkeypatch) -> None:
    # Arrange: set bundle dir and signing key

    monkeypatch.setenv("PROOF_BUNDLE_DIR", str(tmp_path))

    sk = Ed25519PrivateKey.generate()

    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")

    monkeypatch.setenv("ED25519_PRIVKEY_PEM", pem)

    rid = "case-001"

    smt2_hash = "a" * 64

    lfsc = "(lfsc)"

    body = {
        "rid": rid,
        "smt2_hash": smt2_hash,
        "lfsc": lfsc,
        "drat": None,
        "merkle_proof": [],
    }

    # Act

    r = client.post("/v1/pco/bundle", json=body)

    assert r.status_code == 200, r.text

    data = r.json()

    assert data["ok"] is True

    # Assert: file exists and contains a ProofBundle that validates

    out_path = tmp_path / f"{rid}.json"

    assert out_path.exists()

    bundle = json.loads(out_path.read_text(encoding="utf-8"))

    # Keep backward-compatibility fields

    assert bundle["rid"] == rid

    assert bundle["smt2_hash"] == smt2_hash

    assert "lfsc" in bundle

    assert isinstance(bundle.get("signature"), str)

    # Validate ProofBundle v0.2

    schema_path = Path(__file__).resolve().parents[2] / "services" / "api_gateway" / "schemas" / "proofbundle_v0.2.json"

    schema = json.loads(schema_path.read_text(encoding="utf-8"))

    Draft202012Validator(schema).validate(bundle)
