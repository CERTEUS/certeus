#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/schemas/test_dpco_mco_schemas.py               |

# | ROLE: Test module.                                          |

# | PLIK: tests/schemas/test_dpco_mco_schemas.py               |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Testy walidacji przykładowych obiektów wg schematów DPCO/MCO.

EN: Schema validation tests for example DPCO/MCO objects.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft7Validator

# === TESTY / TESTS ===


def _repo() -> Path:
    return Path(__file__).resolve().parents[2]


def test_dpco_mco_schemas_validate_examples() -> None:
    # Load schemas
    dpco_schema = json.loads(
        (_repo() / "schemas" / "data_pco_v0.1.json").read_text(encoding="utf-8")
    )
    mco_schema = json.loads(
        (_repo() / "schemas" / "model_pco_v0.1.json").read_text(encoding="utf-8")
    )

    # Create validators
    v_dpco = Draft7Validator(dpco_schema)  # type: ignore[call-arg]
    v_mco = Draft7Validator(mco_schema)  # type: ignore[call-arg]

    # Valid DPCO
    dpco = {
        "dataset_hash": "sha256:" + ("0" * 64),
        "lineage": ["io.email.mail_id", "cfe.geodesic_action"],
        "dp_epsilon": 0.5,
        "consent_refs": ["consent://demo"],
    }
    v_dpco.validate(dpco)  # should not raise

    # Valid MCO (references DPCO objects)
    mco = {
        "training": {
            "data_dpco": [dpco],
            "sbom_uri": "file://sbom.json",
            "commit_sha": "deadbee",
        },
        "eval": {"ece": 0.01, "brier": 0.05, "auroc": 0.9},
        "bias_report_uri": "https://example.invalid/report",
    }
    v_mco.validate(mco)
