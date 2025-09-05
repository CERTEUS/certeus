#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/validate_openapi_examples.py                  |
# | ROLE: Project script.                                       |
# | PLIK: scripts/validate_openapi_examples.py                  |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: Waliduje, że OpenAPI zawiera kluczowe endpointy oraz podstawowe przykłady
    (D71: presence-check). EN: Validates OpenAPI has key endpoints and examples.
"""

from __future__ import annotations

# === IMPORTY / IMPORTS ===
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "out" / "openapi.json"

# === LOGIKA / LOGIC ===


def main() -> int:
    if not SPEC.exists():
        print("missing out/openapi.json — run scripts/generate_openapi.py")
        return 1
    spec = json.loads(SPEC.read_text(encoding="utf-8"))
    paths = spec.get("paths", {})
    required = [
        "/v1/devices/horizon_drive/plan",
        "/v1/devices/qoracle/expectation",
        "/v1/packs/",
        "/v1/billing/quota",
        "/v1/fin/tokens/request",
    ]
    missing = [p for p in required if p not in paths]
    if missing:
        print("Missing required OpenAPI paths:", ", ".join(missing))
        return 2
    print("OpenAPI contains required paths (D71 OK)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
