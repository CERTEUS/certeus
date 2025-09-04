#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/w1_demo.py                             |
# | ROLE: Week 1 demo (ingest → analyze → ProofGate → Ledger)   |
# | PLIK: scripts/smokes/w1_demo.py                             |
# | ROLA: Demo Tygodnia 1 (ingest → analiza → ProofGate → Ledger)|
# +-------------------------------------------------------------+
"""
PL: Szybki, lokalny demo-flow tygodnia W1:
    1) MailOps ingest (io.email.* trafia do Ledger)
    2) ChatOps komenda cfe.geodesic (PCO header + Ledger input)
    3) ProofGate publish (minimalny PCO spełniający próg → PUBLISH) + Ledger event

EN: Quick local Week-1 demo flow:
    1) MailOps ingest (io.email.* recorded to Ledger)
    2) ChatOps cfe.geodesic command (PCO header + Ledger input)
    3) ProofGate publish (minimal PCO meeting threshold → PUBLISH) + Ledger event
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from typing import Any


def _ensure_repo_on_path() -> None:
    # Add repo-root for in-proc imports (as per AGENTS README note)
    from pathlib import Path as _P
    import sys as _sys

    _sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402


_ensure_repo_on_path()

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app as gateway_app  # noqa: E402
from services.proofgate.app import app as proofgate_app  # noqa: E402


def _pp(title: str, data: Any) -> None:
    print(f"\n== {title} ==")
    try:
        print(json.dumps(data, indent=2, ensure_ascii=False))
    except Exception:
        print(str(data))


def main() -> int:
    # Enforce Proof-Only I/O for protected endpoints during the demo
    os.environ.setdefault("STRICT_PROOF_ONLY", "1")

    gw = TestClient(gateway_app)
    pg = TestClient(proofgate_app)

    # 1) MailOps ingest → Ledger input
    mail_req = {
        "mail_id": "MSG-001",
        "thread_id": "THREAD-001",
        "from_addr": "sender@example.com",
        "to": ["dest@example.com"],
        "subject": "Hello CERTEUS",
        "spf": "pass",
        "dkim": "pass",
        "dmarc": "pass",
        "attachments": [],
    }
    r1 = gw.post("/v1/mailops/ingest", json=mail_req)
    r1.raise_for_status()
    _pp("MailOps ingest", r1.json())

    # 2) ChatOps → cfe.geodesic
    r2 = gw.post("/v1/chatops/command", json={"cmd": "cfe.geodesic", "args": {}})
    r2.raise_for_status()
    _pp("ChatOps cfe.geodesic", r2.json())

    # 3) ProofGate publish → minimal PCO satisfying policy thresholds
    pco = {
        "case_id": "CER-LEX-DEMO-0001",
        "domain": "lex",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
        "sources": [{"digest": "sha256:deadbeef", "retrieved_at": "2025-09-04T12:00:00Z"}],
        "derivations": [
            {
                "solver": "z3",
                "proof_format": "DRAT",
                "artifact_digest": "sha256:cafebabe",
            }
        ],
        "reproducibility": {
            "image": "docker.io/certeus/proof:demo",
            "image_digest": "sha256:012345",
            "seed": "42",
        },
        "signatures": [{"role": "counsel", "name": "Demo Counsel", "sig": "stub"}],
    }
    pub_req = {"pco": pco, "budget_tokens": 1}
    r3 = pg.post("/v1/proofgate/publish", json=pub_req)
    r3.raise_for_status()
    _pp("ProofGate publish", r3.json())

    status = (r3.json() or {}).get("status")
    if status != "PUBLISH":
        print(f"\nWARN: Expected PUBLISH, got {status!r}")

    # Optional: check ProofGate health and API Gateway health
    r_h1 = pg.get("/healthz")
    r_h2 = gw.get("/health")
    _pp("ProofGate /healthz", r_h1.json())
    _pp("Gateway /health", r_h2.json())

    print("\nOK: Week-1 demo complete (ingest -> analyze -> publish)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
