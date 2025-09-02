#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/smoke_stack.py                              |

# | ROLE: Project module.                                       |

# | PLIK: scripts/smoke_stack.py                              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from hashlib import sha256
import os
import random
import string
import sys
import time

import requests

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


BASE = os.getenv("CER_BASE", "http://127.0.0.1:8000").rstrip("/")


def _wait(url: str, timeout: float = 30.0) -> None:
    t0 = time.time()

    while time.time() - t0 < timeout:
        try:
            r = requests.get(url, timeout=2)

            if r.status_code < 500:
                return

        except Exception:
            pass

        time.sleep(1)

    raise RuntimeError(f"Service at {url} not ready")


def _rid(prefix: str = "case") -> str:
    return f"{prefix}-" + "".join(random.choices(string.ascii_lowercase + string.digits, k=6))


def main() -> int:
    try:
        # 1) Wait for API

        _wait(BASE + "/health", timeout=60)

        # 2) ProofGate publish (via API route)

        pco = {"case_id": _rid(), "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05}}

        r = requests.post(
            BASE + "/v1/proofgate/publish",
            json={"pco": pco, "budget_tokens": 10},
            timeout=10,
        )

        r.raise_for_status()

        body = r.json()

        assert body.get("status") in {"PUBLISH", "CONDITIONAL", "PENDING", "ABSTAIN"}

        # 3) Ledger record/list/prove

        case_id = _rid("ledger")

        doc_hash = "sha256:" + sha256(b"doc").hexdigest()

        r = requests.post(
            BASE + "/v1/ledger/record-input",
            json={"case_id": case_id, "document_hash": doc_hash},
            timeout=10,
        )

        r.raise_for_status()

        r = requests.get(BASE + f"/v1/ledger/{case_id}/records", timeout=10)

        r.raise_for_status()

        r = requests.get(BASE + f"/v1/ledger/{case_id}/prove", timeout=10)

        assert r.status_code in (200, 404)  # ok if no records or schema disabled

        # 4) Metrics scrape

        for target in (BASE + "/metrics",):
            r = requests.get(target, timeout=10)

            r.raise_for_status()

            assert "certeus_abstain_rate" in r.text

        # 5) Optional bundle creation if keys are present

        if os.getenv("ED25519_PRIVKEY_PEM"):
            rid = _rid("bundle")

            smt2_hash = sha256(b"(set-logic ALL) (check-sat)").hexdigest()

            r = requests.post(
                BASE + "/v1/pco/bundle",
                json={"rid": rid, "smt2_hash": smt2_hash, "lfsc": "(lfsc proof)", "merkle_proof": []},
                timeout=15,
            )

            r.raise_for_status()

        return 0

    except Exception as e:
        print(f"SMOKE FAILED: {e}")

        return 1


if __name__ == "__main__":
    sys.exit(main())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
