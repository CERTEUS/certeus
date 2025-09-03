#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/gates/test_redaction_gate_cli.py               |

# | ROLE: Test module.                                          |

# | PLIK: tests/gates/test_redaction_gate_cli.py               |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Testy CLI gate'u redakcji (PII) — wykrywanie i polityka STRICT.

EN: Tests for redaction gate CLI (PII) — detection and STRICT policy.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

# === TESTY / TESTS ===


def _repo() -> Path:
    return Path(__file__).resolve().parents[2]


def _run_gate(payload: dict, strict: bool) -> int:
    env = os.environ.copy()
    env["STRICT_REDACTION"] = "1" if strict else "0"
    proc = subprocess.run(
        [sys.executable, str(_repo() / "scripts" / "gates" / "redaction_gate.py")],
        input=json.dumps(payload),
        text=True,
        capture_output=True,
        env=env,
    )
    # Return code conveys detection/strict policy
    return proc.returncode


def test_redaction_gate_detects_pii_and_enforces_strict() -> None:
    pii_payload = {"subject": {"name": "PESEL: 12345678901"}}
    # Non-strict: detection but exit 0
    rc = _run_gate(pii_payload, strict=False)
    assert rc == 0
    # Strict: exit 1
    rc2 = _run_gate(pii_payload, strict=True)
    assert rc2 == 1


def test_redaction_gate_ok_on_clean_payload() -> None:
    clean_payload = {"subject": {"name": "Jan TEST"}, "content": "Brak wrazliwych danych."}
    assert _run_gate(clean_payload, strict=False) == 0
    assert _run_gate(clean_payload, strict=True) == 0
