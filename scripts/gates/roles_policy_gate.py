#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/roles_policy_gate.py                   |
# | ROLE: Project gate script (fine-grained roles check).       |
# | PLIK: scripts/gates/roles_policy_gate.py                   |
# | ROLA: Skrypt bramki (sprawdzenie ról fine-grained).         |
# +-------------------------------------------------------------+

"""
PL: Bramkę ról (proxy OPA) traktujemy jako szkic: dopuszczamy akcje
    bazując na roli użytkownika. Używa wejścia JSON (stdin) lub
    wartości domyślnych.

EN: Fine-grained roles gate (OPA proxy skeleton): allows actions
    based on user's role. Consumes JSON from stdin or defaults.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import sys
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===
ALLOWED_ROLES: set[str] = {"AFV", "ASE", "ATC", "ATS", "AVR"}


# === LOGIKA / LOGIC ===
def _read_input() -> dict[str, Any]:
    try:
        raw = sys.stdin.read().strip()
        if raw:
            return json.loads(raw)
    except Exception:
        pass
    return {
        "user": {"id": "robot", "role": "AFV"},
        "action": "publish",
        "resource": {"kind": "pco", "case_id": "CER-LEX-99"},
    }


def _allow(user_role: str, action: str) -> bool:
    if user_role not in ALLOWED_ROLES:
        return False
    if action == "read":
        return True
    if action == "publish":
        return True
    if action == "merge":
        return user_role in {"ATC", "ASE"}
    # default deny for unknown actions
    return False


def main() -> int:
    data = _read_input()
    user = (data.get("user") or {}) if isinstance(data, dict) else {}
    role = str(user.get("role") or "").strip()
    action = str((data.get("action") or "").strip())

    if not role or not action:
        print("Roles Gate: FAIL missing role/action")
        return 1

    if _allow(role, action):
        print(f"Roles Gate: OK ({role} may {action})")
        return 0

    print(f"Roles Gate: FAIL role {role} not permitted for {action}")
    return 1


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
