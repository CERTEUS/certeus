#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_proofgate_decision.py           |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_proofgate_decision.py           |

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

from fastapi.testclient import TestClient

from services.ledger_service.ledger import ledger_service
from services.proofgate.app import app

client = TestClient(app)

def _minimal_pco(case_id: str, with_counsel: bool = True) -> dict:
    pco = {
        "case_id": case_id,
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
        "sources": [
            {"id": "s1", "uri": "hash://sha256/aa", "digest": "a" * 64, "retrieved_at": "2025-01-01T00:00:00Z"}
        ],
        "derivations": [{"claim_id": "c1", "solver": "z3", "proof_format": "LFSC", "artifact_digest": "b" * 64}],
        "reproducibility": {"image": "img:dev", "image_digest": "sha256:deadbeef", "seed": "0"},
        "signatures": [
            {"role": "producer", "alg": "ed25519", "key_id": "kid1", "signature": "sig1"},
        ],
    }

    if with_counsel:
        pco["signatures"].append({"role": "counsel", "alg": "ed25519", "key_id": "kid2", "signature": "sig2"})

    return pco

def test_publish_when_policy_and_budget_ok_and_counsel_present() -> None:
    pco = _minimal_pco("case-123", with_counsel=True)

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})

    assert r.status_code == 200, r.text

    body = r.json()

    assert body["status"] == "PUBLISH"

    assert isinstance(body.get("ledger_ref"), str) and len(body["ledger_ref"]) == 64

    records = ledger_service.get_records_for_case(case_id="case-123")

    assert any(rec.get("type") == "PCO_PUBLISH" and rec.get("chain_self") == body["ledger_ref"] for rec in records)

def test_abstain_when_missing_counsel_signature() -> None:
    pco = _minimal_pco("case-124", with_counsel=False)

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})

    assert r.status_code == 200, r.text

    assert r.json()["status"] == "ABSTAIN"

def test_abstain_when_sources_missing_digest_or_retrieved_at() -> None:
    pco = _minimal_pco("case-125", with_counsel=True)

    pco["sources"][0].pop("digest")

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})

    assert r.status_code == 200, r.text

    assert r.json()["status"] == "ABSTAIN"

def test_abstain_when_solver_not_allowed() -> None:
    pco = _minimal_pco("case-126", with_counsel=True)

    pco["derivations"][0]["solver"] = "other"

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})

    assert r.status_code == 200, r.text

    assert r.json()["status"] == "ABSTAIN"

def test_abstain_when_any_risk_exceeds() -> None:
    pco = {
        "risk": {"ece": 0.03, "brier": 0.05, "abstain_rate": 0.05},
    }

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 10})

    assert r.status_code == 200, r.text

    assert r.json()["status"] == "ABSTAIN"

def test_pending_when_no_budget_but_good_risk() -> None:
    pco = _minimal_pco("case-200", with_counsel=False)

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 0})

    assert r.status_code == 200, r.text

    assert r.json()["status"] == "PENDING"

def test_conditional_when_missing_risk() -> None:
    pco = {"something_else": True}

    r = client.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 5})

    assert r.status_code == 200, r.text

    assert r.json()["status"] == "CONDITIONAL"
