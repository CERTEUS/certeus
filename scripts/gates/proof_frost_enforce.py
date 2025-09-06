#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/proof_frost_enforce.py                 |
# | ROLE: CI Gate — enforce FROST quorum in publish            |
# | PLIK: scripts/gates/proof_frost_enforce.py                 |
# | ROLA: Bramka CI — egzekwuje quorum FROST przy publish      |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
from typing import Any

from fastapi.testclient import TestClient

from security.frost import aggregate
from services.proofgate.app import app


def _base_ok_pco() -> dict[str, Any]:
    return {
        "domain": "lex",
        "case_id": "CER-LEX-FROST-GATE",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
        "sources": [
            {
                "id": "s1",
                "uri": "hash://sha256/aa",
                "digest": "a" * 64,
                "retrieved_at": "2025-01-01T00:00:00Z",
            }
        ],
        "derivations": [
            {
                "claim_id": "c1",
                "solver": "z3",
                "proof_format": "LFSC",
                "artifact_digest": "b" * 64,
            }
        ],
        "reproducibility": {
            "image": "img:dev",
            "image_digest": "sha256:deadbeef",
            "seed": "0",
        },
        "signatures": [
            {
                "role": "producer",
                "alg": "ed25519",
                "key_id": "kid1",
                "signature": "sig1",
            },
            {
                "role": "counsel",
                "alg": "ed25519",
                "key_id": "kid2",
                "signature": "sig2",
            },
        ],
    }


def main() -> None:
    out_dir = Path("out")
    out_dir.mkdir(parents=True, exist_ok=True)
    # Enforce FROST gate
    os.environ["REQUIRE_COSIGN_ATTESTATIONS"] = "1"
    client = TestClient(app)
    # Case 1: missing quorum → ABSTAIN
    pco_bad = _base_ok_pco()
    r1 = client.post(
        "/v1/proofgate/publish", json={"pco": pco_bad, "budget_tokens": 10}
    )
    ok1 = r1.status_code == 200 and r1.json().get("status") == "ABSTAIN"
    # Case 2: quorum present → PUBLISH
    pco_ok = _base_ok_pco()
    fq = aggregate(["kidA", "kidB"], threshold=2, participants=3)
    pco_ok["cosign"] = fq.to_dict()
    r2 = client.post("/v1/proofgate/publish", json={"pco": pco_ok, "budget_tokens": 10})
    ok2 = r2.status_code == 200 and r2.json().get("status") == "PUBLISH"
    report = {"missing_quorum_abstain": ok1, "with_quorum_publish": ok2}
    (out_dir / "proof_frost_enforce.json").write_text(
        json.dumps(report, indent=2), encoding="utf-8"
    )
    if not (ok1 and ok2):
        print("FROST Gate failed:", report, file=sys.stderr)
        sys.exit(1)
    (out_dir / "proof_frost_enforce_ok.txt").write_text("ok\n", encoding="utf-8")


if __name__ == "__main__":  # pragma: no cover
    main()
