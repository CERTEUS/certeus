# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/e2e/test_smoke_endpoints.py                   |

# | ROLE: Project module.                                       |

# | PLIK: tests/e2e/test_smoke_endpoints.py                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

from __future__ import annotations

import os
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient
import pytest


def _gen_ed25519() -> tuple[str, str]:
    sk = Ed25519PrivateKey.generate()

    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")

    pub = sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)

    return pem, pub.hex()


@pytest.fixture(scope="module")
def client(tmp_path_factory: pytest.TempPathFactory) -> TestClient:
    # Prepare environment (bundle dir, keys, caches)

    bundle_dir = tmp_path_factory.mktemp("public_pco")

    law_cache_dir = tmp_path_factory.mktemp("law_cache")

    pem, pub_hex = _gen_ed25519()

    os.environ["PROOF_BUNDLE_DIR"] = str(bundle_dir)

    os.environ["LAW_CACHE_DIR"] = str(law_cache_dir)

    os.environ["ED25519_PRIVKEY_PEM"] = pem

    os.environ["ED25519_PUBKEY_HEX"] = pub_hex

    # Import after env is set

    from services.api_gateway.main import app

    return TestClient(app)


def test_smoke_core_endpoints(client: TestClient, tmp_path: Path) -> None:
    # health, root, metrics

    assert client.get("/health").status_code == 200

    assert client.get("/").status_code == 200

    assert client.get("/metrics").status_code == 200

    # jwks, packs

    r = client.get("/.well-known/jwks.json")

    assert r.status_code == 200 and "keys" in r.json()

    assert client.get("/v1/packs/").status_code == 200

    # CFE

    assert client.post("/v1/cfe/geodesic", json={"case": "CER-SMOKE", "facts": {}, "norms": {}}).status_code == 200

    assert client.post("/v1/cfe/horizon", json={}).status_code == 200

    assert client.get("/v1/cfe/lensing").status_code == 200

    # QTMP

    assert client.post("/v1/qtm/init_case", json={"basis": ["ALLOW", "DENY", "ABSTAIN"]}).status_code == 200

    assert client.post("/v1/qtm/measure", json={"operator": "W", "source": "ui"}).status_code == 200

    assert client.post("/v1/qtm/commutator", json={"A": "X", "B": "Y"}).status_code == 200

    assert client.post("/v1/qtm/find_entanglement", json={"variables": ["A", "B"]}).status_code == 200

    # Devices

    assert client.post("/v1/devices/horizon_drive/plan", json={}).status_code == 200

    assert (
        client.post(
            "/v1/devices/qoracle/expectation",
            json={"objective": "maximize fairness", "constraints": {}},
        ).status_code
        == 200
    )

    assert (
        client.post(
            "/v1/devices/entangle", json={"variables": ["RISK", "SENTIMENT"], "target_negativity": 0.1}
        ).status_code
        == 200
    )

    assert client.post("/v1/devices/chronosync/reconcile", json={"coords": {"t": 0}, "pc_delta": {}}).status_code == 200

    # Ethics

    assert (
        client.post(
            "/v1/ethics/equity_meter",
            json={"distribution_a": [0.2, 0.8], "distribution_b": [0.5, 0.5]},
        ).status_code
        == 200
    )

    assert (
        client.post(
            "/v1/ethics/double_verdict",
            json={"W_litera": "ALLOW", "T_telos": "TRUTH", "rationale": "smoke"},
        ).status_code
        == 200
    )

    # DR

    assert client.post("/v1/dr/replay", json={"case": "CER-1", "timestamp": "2023-10-01T00:00:00Z"}).status_code == 200

    assert client.post("/v1/dr/recall", json={"upn": "UPN-TEST"}).status_code == 200

    # Export

    assert client.post("/v1/export", json={"case_id": "CER-1", "analysis_result": {"ok": True}}).status_code == 200

    # ChatOps

    assert client.post("/v1/chatops/command", json={"cmd": "cfe.geodesic", "args": {}}).status_code == 200

    # Ledger

    assert (
        client.post(
            "/v1/ledger/record-input",
            json={"case_id": "CER-1", "document_hash": "sha256:" + ("0" * 16)},
        ).status_code
        == 200
    )

    assert client.get("/v1/ledger/CER-1/records").status_code == 200

    assert client.get("/v1/ledger/CER-1/prove").status_code == 200

    # Verify

    smt = "(set-logic QF_UF) (declare-fun x () Bool) (assert x) (check-sat)"

    assert client.post("/v1/verify", json={"formula": smt, "lang": "smt2"}).status_code == 200

    # PCO bundle + public verify

    rid = "RID-SMOKE-TEST"

    payload = {
        "rid": rid,
        "smt2_hash": "0" * 64,
        "lfsc": "(lfsc proof)",
        "drat": "p drat",
        "merkle_proof": [],
    }

    assert client.post("/v1/pco/bundle", json=payload).status_code == 200

    assert client.get(f"/pco/public/{rid}").status_code == 200

    # Preview (multipart)

    files = {"file": ("hello.txt", b"hello", "text/plain")}

    assert client.post("/v1/preview", files=files).status_code == 200

    # Ingest/analyze (PDF minimal)

    pdf_min = b"%PDF-1.4\n1 0 obj<<>>endobj\ntrailer<<>>\n%%EOF"

    files_pdf = {"file": ("doc.pdf", pdf_min, "application/pdf")}

    assert client.post("/v1/ingest", files=files_pdf).status_code == 200

    assert client.post("/v1/analyze?case_id=CER-1", files=files_pdf).status_code == 200
