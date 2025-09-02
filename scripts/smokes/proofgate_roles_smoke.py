#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/proofgate_roles_smoke.py              |
# | ROLE: Smoke: ProofGate role enforcement (lex vs sec)        |
# | PLIK: scripts/smokes/proofgate_roles_smoke.py              |
# | ROLA: Smoke: egzekwowanie ról w ProofGate (lex vs sec)      |
# +-------------------------------------------------------------+

"""
PL: Smoke‑test ProofGate ról: dla domeny lex powinno być PUBLISH,
    a dla sec (publish=[]) — ABSTAIN. Wymaga FINE_GRAINED_ROLES=1.

EN: ProofGate roles smoke: for domain lex expect PUBLISH, for sec expect
    ABSTAIN. Requires FINE_GRAINED_ROLES=1.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os
from typing import Any

from fastapi.testclient import TestClient

from services.proofgate.app import app


# === LOGIKA / LOGIC ===
def _pco(domain: str, case_prefix: str, roles: list[str]) -> dict[str, Any]:
    return {
        "domain": domain,
        "case_id": f"CER-{case_prefix}-SMOKE",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.1},
        "sources": [{"digest": "d1", "retrieved_at": "now"}],
        "derivations": [{"solver": "z3", "proof_format": "LFSC", "artifact_digest": "h"}],
        "reproducibility": {"image": "img", "image_digest": "sha256:deadbeef", "seed": "42"},
        "signatures": [{"role": r} for r in roles],
    }


def main() -> int:
    os.environ["FINE_GRAINED_ROLES"] = "1"
    c = TestClient(app)

    # LEX should publish with AFV + counsel
    r1 = c.post("/v1/proofgate/publish", json={"pco": _pco("lex", "LEX", ["counsel", "AFV"]), "budget_tokens": 10})
    r1.raise_for_status()
    if r1.json().get("status") != "PUBLISH":
        print("ProofGate roles smoke: FAIL (lex expected PUBLISH)")
        return 1

    # SEC should abstain even with AFV + counsel
    r2 = c.post("/v1/proofgate/publish", json={"pco": _pco("sec", "SEC", ["counsel", "AFV"]), "budget_tokens": 10})
    r2.raise_for_status()
    if r2.json().get("status") != "ABSTAIN":
        print("ProofGate roles smoke: FAIL (sec expected ABSTAIN)")
        return 1

    print("ProofGate roles smoke: OK")
    return 0


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
