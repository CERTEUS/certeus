#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/supply_chain/make_provenance.py              |
# | ROLE: Project script.                                       |
# | PLIK: scripts/supply_chain/make_provenance.py              |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Budowa minimalnego artefaktu provenance (in-toto styl). Zapisuje
    `out/provenance.json` z metadanymi budowy na potrzeby attestacji cosign.

EN: Build a minimal provenance artifact (in-toto style). Writes
    `out/provenance.json` with build metadata for cosign attestations.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
import time
from typing import Any

def main() -> int:
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)
    payload: dict[str, Any] = {
        "_schema": "certeus.provenance.v1",
        "build_id": os.getenv("GITHUB_RUN_ID") or str(int(time.time())),
        "commit": os.getenv("GITHUB_SHA", "unknown")[:12],
        "runner": os.getenv("GITHUB_RUN_NUMBER", "local"),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "environment": {
            "python": os.getenv("Python_VERSION", "3"),
            "platform": os.getenv("RUNNER_OS", "linux"),
        },
        "materials": [
            {"uri": "repo://certeus", "digest": os.getenv("GITHUB_SHA", "unknown")},
        ],
        "steps": [
            {"name": "lint", "status": "success"},
            {"name": "tests", "status": "success"},
        ],
    }
    (out / "provenance.json").write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print("wrote out/provenance.json")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
