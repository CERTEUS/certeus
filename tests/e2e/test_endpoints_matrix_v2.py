#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/e2e/test_endpoints_matrix_v2.py                |
# | ROLE: Test module.                                          |
# | PLIK: tests/e2e/test_endpoints_matrix_v2.py                |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Parametryczna macierz testów E2E dla głównych endpointów API,
    aby zwiększyć pokrycie scenariuszy i stabilność smoków.

EN: Parameterized E2E matrix tests for main API endpoints,
    increasing scenario coverage and smoke stability.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

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
    # Przygotowanie środowiska (bundle, cache, klucze)
    bundle_dir = tmp_path_factory.mktemp("public_pco")
    law_cache_dir = tmp_path_factory.mktemp("law_cache")
    pem, pub_hex = _gen_ed25519()

    os.environ["PROOF_BUNDLE_DIR"] = str(bundle_dir)
    os.environ["LAW_CACHE_DIR"] = str(law_cache_dir)
    os.environ["ED25519_PRIVKEY_PEM"] = pem
    os.environ["ED25519_PUBKEY_HEX"] = pub_hex

    from services.api_gateway.main import app

    return TestClient(app)

# === KONFIGURACJA / CONFIGURATION ===

GET_ENDPOINTS = [
    "/health",
    "/metrics",
    "/openapi.json",
    "/.well-known/jwks.json",
    "/v1/packs/",
    "/v1/cfe/lensing",
    "/v1/lexqft/coverage",
]

POST_JSON_ENDPOINTS: list[tuple[str, dict[str, Any]]] = [
    ("/v1/cfe/geodesic", {"case": "CER-M", "facts": {}, "norms": {}}),
    ("/v1/cfe/horizon", {}),
    ("/v1/qtm/init_case", {"basis": ["ALLOW", "DENY", "ABSTAIN"]}),
    ("/v1/qtm/measure", {"operator": "W", "source": "ui"}),
    ("/v1/qtm/commutator", {"A": "X", "B": "Y"}),
    ("/v1/qtm/find_entanglement", {"variables": ["A", "B"]}),
    ("/v1/devices/horizon_drive/plan", {}),
    ("/v1/devices/qoracle/expectation", {"objective": "maximize fairness", "constraints": {}}),
    ("/v1/devices/entangle", {"variables": ["RISK", "SENTIMENT"], "target_negativity": 0.1}),
    ("/v1/devices/chronosync/reconcile", {"coords": {"t": 0}, "pc_delta": {}}),
    ("/v1/ethics/equity_meter", {"distribution_a": [0.2, 0.8], "distribution_b": [0.5, 0.5]}),
    ("/v1/ethics/double_verdict", {"W_litera": "ALLOW", "T_telos": "TRUTH", "rationale": "smoke"}),
    ("/v1/dr/replay", {"case": "CER-1", "timestamp": "2023-10-01T00:00:00Z"}),
    ("/v1/dr/recall", {"upn": "UPN-TEST"}),
    ("/v1/export", {"case_id": "CER-1", "analysis_result": {"ok": True}}),
    ("/v1/verify", {"formula": "(set-logic QF_UF) (assert true) (check-sat)", "lang": "smt2"}),
    ("/v1/lexqft/coverage/update", [{"gamma": 0.9, "weight": 1.0, "uncaptured": 0.05}]),
    ("/v1/lexqft/coverage/reset", {}),
    # Ledger input (valid sha256 placeholder)
    ("/v1/ledger/record-input", {"case_id": "CER-1", "document_hash": "sha256:" + ("0" * 64)}),
]

# === LOGIKA / LOGIC ===

@pytest.mark.parametrize("path", GET_ENDPOINTS, ids=[p for p in GET_ENDPOINTS])
def test_get_endpoints_respond_2xx(client: TestClient, path: str) -> None:
    r = client.get(path)
    assert 200 <= r.status_code < 300

@pytest.mark.parametrize(
    "path,payload",
    POST_JSON_ENDPOINTS,
    ids=[p for p, _ in POST_JSON_ENDPOINTS],
)
def test_post_endpoints_json_2xx(client: TestClient, path: str, payload: dict[str, Any] | list[dict[str, Any]]) -> None:
    r = client.post(path, json=payload)
    assert 200 <= r.status_code < 300

def test_post_preview_and_ingest_minimal_pdf(client: TestClient, tmp_path: Path) -> None:
    # Preview
    files = {"file": ("hello.txt", b"hello", "text/plain")}
    rp = client.post("/v1/preview", files=files)
    assert 200 <= rp.status_code < 300
    # Ingest minimal PDF + analyze
    pdf_min = b"%PDF-1.4\n1 0 obj<<>>endobj\ntrailer<<>>\n%%EOF"
    files_pdf = {"file": ("doc.pdf", pdf_min, "application/pdf")}
    ri = client.post("/v1/ingest", files=files_pdf)
    assert 200 <= ri.status_code < 300
    ra = client.post("/v1/analyze?case_id=CER-M", files=files_pdf)
    assert 200 <= ra.status_code < 300

@pytest.mark.parametrize("e", [0.0, 0.2, 0.6, 1.0, 2.0], ids=lambda x: f"E={x}")
def test_lexqft_tunnel_energy_bounds(client: TestClient, e: float) -> None:
    r = client.post("/v1/lexqft/tunnel", json={"evidence_energy": e})
    assert r.status_code == 200
    js = r.json()
    p = float(js.get("p_tunnel", -1))
    assert 0.0 <= p <= 0.95

@pytest.mark.parametrize(
    "neg,vars_",
    [
        (0.05, ["A", "B"]),
        (0.10, ["RISK", "SENTIMENT"]),
        (0.20, ["X", "Y", "Z"]),
        (0.50, ["U", "V"]),
    ],
    ids=["n=0.05", "n=0.10", "n=0.20", "n=0.50"],
)
def test_devices_entangle_negativity_bounds(client: TestClient, neg: float, vars_: list[str]) -> None:
    r = client.post("/v1/devices/entangle", json={"variables": vars_, "target_negativity": neg})
    assert r.status_code == 200
    val = float(r.json().get("achieved_negativity", 0.0))
    assert 0.0 <= val <= 0.12

@pytest.mark.parametrize(
    "question",
    [
        "Should we appeal?",
        "Optimize fairness under constraints",
        "Minimize risk of mismatch",
        "Balance coverage and cost",
        "Select device schedule",
        "Entropy heuristic",
        "Evidence weighting",
        "Policy compliance",
        "Redaction strategy",
        "Boundary drill",
        "Case planning",
        "Adversarial outcome",
        "Multi-criteria decision",
        "Budget allocation",
        "Juridical scope",
        "Signal attenuation",
        "Horizon lock",
        "Coverage raising",
        "Uncertainty bound",
        "Entanglement strength",
        "Chronosync clause",
    ],
)
def test_devices_qoracle_various_questions(client: TestClient, question: str) -> None:
    r = client.post("/v1/devices/qoracle/expectation", json={"question": question})
    assert r.status_code == 200
    js = r.json()
    assert "optimum" in js and isinstance(js.get("distribution"), list)

@pytest.mark.parametrize(
    "op,src",
    [
        ("W", "ui"),
        ("I", "planner"),
        ("C", "sim"),
        ("L", "api"),
        ("T", "api"),
        ("W", "batch"),
        ("I", "cli"),
        ("C", "test"),
        ("L", "dev"),
        ("T", "dev"),
    ],
)
def test_qtm_measure_various_operators(client: TestClient, op: str, src: str) -> None:
    r = client.post("/v1/qtm/measure", json={"operator": op, "source": src})
    assert r.status_code == 200

@pytest.mark.parametrize(
    "spf,dkim,dmarc,att_count",
    [
        ("pass", "pass", "pass", 0),
        ("pass", "fail", "none", 1),
        ("softfail", "pass", "quarantine", 2),
        (None, None, None, 3),
    ],
)
def test_mailops_ingest_variants(
    client: TestClient, spf: str | None, dkim: str | None, dmarc: str | None, att_count: int
) -> None:
    atts = [{"filename": f"a{i}.txt", "content_type": "text/plain", "size": 5 + i} for i in range(att_count)]
    r = client.post(
        "/v1/mailops/ingest",
        json={
            "mail_id": "mid-1",
            "thread_id": "thr-1",
            "from_addr": "a@example.com",
            "to": ["b@example.com"],
            "subject": "Test",
            "body_text": "Hello",
            "spf": spf,
            "dkim": dkim,
            "dmarc": dmarc,
            "attachments": atts,
        },
    )
    assert r.status_code == 200
    js = r.json()
    assert js.get("ok") is True
    io = js.get("io", {})
    assert isinstance(io.get("attachments"), list)

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
