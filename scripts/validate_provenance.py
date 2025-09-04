#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/validate_provenance.py                        |
# | ROLE: Validate provenance.json against schema                |
# | PLIK: scripts/validate_provenance.py                        |
# | ROLA: Walidacja provenance.json wg schematu                  |
# +-------------------------------------------------------------+

"""
PL: Waliduje `out/provenance.json` względem `schemas/certeus.provenance.v1.json`.
    Używa jsonschema; zwraca kod !=0, gdy walidacja się nie powiedzie.

EN: Validates `out/provenance.json` against `schemas/certeus.provenance.v1.json`.
    Uses jsonschema; returns non-zero exit code on failure.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    prov_p = repo / "out" / "provenance.json"
    schema_p = repo / "schemas" / "certeus.provenance.v1.json"
    if not prov_p.exists():
        print("provenance: missing out/provenance.json")
        return 1
    try:
        data = json.loads(prov_p.read_text(encoding="utf-8"))
        schema = json.loads(schema_p.read_text(encoding="utf-8"))
        Draft202012Validator(schema).validate(data)
        print("provenance: OK")
        return 0
    except Exception as e:
        print(f"provenance: INVALID: {e}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
