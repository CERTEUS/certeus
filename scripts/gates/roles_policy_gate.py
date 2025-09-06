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
import os
from pathlib import Path
import sys
from typing import Any

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

# === KONFIGURACJA / CONFIGURATION ===

ALLOWED_ROLES: set[str] = {"AFV", "ASE", "ATC", "ATS", "AVR"}
DEFAULT_DOMAIN = os.getenv("GOV_DOMAIN") or "lex"
DEFAULT_GOV_PACK = os.getenv("GOV_PACK") or str(
    Path(__file__).resolve().parents[2]
    / "policies"
    / "governance"
    / "governance_pack.v0.1.yaml"
)

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


def _load_governance() -> dict[str, Any] | None:
    if not yaml:
        return None
    p = Path(DEFAULT_GOV_PACK)
    if not p.exists():
        return None
    try:
        return yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    except Exception:
        return None


def _allow_by_pack(
    role: str, action: str, resource_kind: str, scope: str | None
) -> bool | None:
    pack = _load_governance()
    if not pack:
        return None
    dom = (scope or DEFAULT_DOMAIN or "lex").strip()
    dom_cfg = (pack.get("domains") or {}).get(dom)
    if not isinstance(dom_cfg, dict):
        return None
    allow_map = dom_cfg.get("allow") or {}
    if not isinstance(allow_map, dict):
        return None
    allowed_roles = allow_map.get(action)
    if not isinstance(allowed_roles, list):
        return None
    return role in set(map(str, allowed_roles))


def _allow(
    user_role: str, action: str, *, resource_kind: str, scope: str | None
) -> bool:
    # Governance pack first (if present)
    by_pack = _allow_by_pack(user_role, action, resource_kind, scope)
    if isinstance(by_pack, bool):
        return by_pack
    # Fallback to built-in skeleton
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
    resource = (data.get("resource") or {}) if isinstance(data, dict) else {}
    rkind = str(resource.get("kind") or "pco")
    scope = resource.get("scope")

    if not role or not action:
        print("Roles Gate: FAIL missing role/action")
        return 1

    if _allow(role, action, resource_kind=rkind, scope=scope):
        print(f"Roles Gate: OK ({role} may {action})")
        return 0

    print(f"Roles Gate: FAIL role {role} not permitted for {action}")
    return 1


# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
