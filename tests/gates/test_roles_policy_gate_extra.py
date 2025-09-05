#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/gates/test_roles_policy_gate_extra.py          |

# | ROLE: Test module.                                          |

# | PLIK: tests/gates/test_roles_policy_gate_extra.py          |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Dodatkowe testy gate'u polityk ról w governance pack'u.

EN: Extra tests for roles policy gate using the governance pack.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys

# === TESTY / TESTS ===


def _repo() -> Path:
    return Path(__file__).resolve().parents[2]


def _run(payload: dict) -> int:
    proc = subprocess.run(
        [sys.executable, str(_repo() / "scripts" / "gates" / "roles_policy_gate.py")],
        input=json.dumps(payload),
        text=True,
        capture_output=True,
    )
    return proc.returncode


def test_roles_gate_pack_allows_publish_for_afv_in_lex() -> None:
    # Governance pack allows AFV to publish in lex domain
    payload = {"user": {"role": "AFV"}, "action": "publish", "resource": {"kind": "pco", "scope": "lex"}}
    assert _run(payload) == 0


def test_roles_gate_denies_merge_for_non_privileged() -> None:
    for role in ["AFV", "AVR", "ATS"]:
        payload = {"user": {"role": role}, "action": "merge", "resource": {"kind": "pco", "scope": "lex"}}
        assert _run(payload) == 1
