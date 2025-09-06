#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/schemas/test_security_pco_schema.py            |

# | ROLE: Test module.                                          |

# | PLIK: tests/schemas/test_security_pco_schema.py            |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Test walidacji przykładowego obiektu wg schematu Security‑PCO (SEC) v0.1.

EN: Validation test for an example object against Security‑PCO (SEC) v0.1 schema.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft7Validator

# === TESTY / TESTS ===


def _repo() -> Path:
    return Path(__file__).resolve().parents[2]


def test_security_pco_schema_valid_example() -> None:
    schema = json.loads(
        (_repo() / "schemas" / "security_pco_v0.1.json").read_text(encoding="utf-8")
    )
    validator = Draft7Validator(schema)  # type: ignore[call-arg]

    sec = {
        "finding_id": "SEC-0001",
        "severity": "HIGH",
        "status": "OPEN",
        "controls": ["ISO27001:A.12.6", "SOC2:Security"],
        "evidence": [
            {
                "digest": "sha256:" + ("a" * 64),
                "type": "artifact",
                "uri": "pfs://mail/M-1/rep.pdf",
            }
        ],
        "cwe": ["CWE-79"],
        "cve": ["CVE-2025-0001"],
        "cvss": 8.2,
        "attestation": {"tee": True},
    }

    # Should not raise
    validator.validate(sec)
