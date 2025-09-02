from __future__ import annotations

"""
PL: Testy enforcementu ról w ProofGate na podstawie Governance Pack.
EN: ProofGate role enforcement tests based on the Governance Pack.
"""

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_proofgate_roles_enforcement.py   |
# | ROLE: Tests for ProofGate governance-aware role checks       |
# | PLIK: tests/services/test_proofgate_roles_enforcement.py   |
# | ROLA: Testy sprawdzeń ról w ProofGate wg Governance         |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
import os  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.proofgate.app import app  # noqa: E402


# === LOGIKA / LOGIC ===
def _minimal_ok_pco(domain: str, case_prefix: str) -> dict:
    case = f"CER-{case_prefix}-TEST"
    return {
        "domain": domain,
        "case_id": case,
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.1},
        "sources": [{"digest": "d1", "retrieved_at": "now"}],
        "derivations": [{"solver": "z3", "proof_format": "LFSC", "artifact_digest": "h"}],
        "reproducibility": {"image": "img", "image_digest": "sha256:deadbeef", "seed": "42"},
        "signatures": [{"role": "counsel"}, {"role": "AFV"}],
    }


# === TESTY / TESTS ===
def test_publish_denied_for_sec_domain_even_with_afv() -> None:
    # Governance: sec.publish is [] (empty) → ABSTAIN
    os.environ["FINE_GRAINED_ROLES"] = "1"
    try:
        client = TestClient(app)
        pco = _minimal_ok_pco("sec", "SEC")
        resp = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
        assert resp.status_code == 200
        body = resp.json()
        assert body["status"] == "ABSTAIN"
    finally:
        os.environ.pop("FINE_GRAINED_ROLES", None)


def test_publish_allowed_for_lex_with_afv_and_counsel() -> None:
    os.environ["FINE_GRAINED_ROLES"] = "1"
    try:
        client = TestClient(app)
        pco = _minimal_ok_pco("lex", "LEX")
        resp = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})
        assert resp.status_code == 200
        body = resp.json()
        assert body["status"] == "PUBLISH"
    finally:
        os.environ.pop("FINE_GRAINED_ROLES", None)
