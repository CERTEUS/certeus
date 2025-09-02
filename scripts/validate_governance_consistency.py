#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/validate_governance_consistency.py           |
# | ROLE: Validator: governance pack ↔ roles gate/rego          |
# | PLIK: scripts/validate_governance_consistency.py           |
# | ROLA: Walidator: governance pack ↔ bramka ról/rego          |
# +-------------------------------------------------------------+

"""
PL: Sprawdza spójność Governance Pack z bramką ról i szkicem rego.
 - Porównuje zbiory ról/akcji z policies/security/roles.rego.
 - Dodatkowo uruchamia roles_policy_gate.py dla par (domena,akcja,rola)
   i weryfikuje, że gate pozwala/odrzuca zgodnie z packiem.

EN: Validates Governance Pack against the roles gate and rego skeleton.
 - Compares roles/actions sets with policies/security/roles.rego.
 - Executes roles_policy_gate.py for (domain,action,role) and checks
   allow/deny per governance pack.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Any

import yaml  # type: ignore


# === LOGIKA / LOGIC ===
def _repo() -> Path:
    # File is at repo_root/scripts/validate_governance_consistency.py → parents[1] == repo_root
    return Path(__file__).resolve().parents[1]


def _load_pack(p: Path) -> dict[str, Any]:
    return yaml.safe_load(p.read_text(encoding="utf-8")) or {}


def _parse_rego_sets(p: Path) -> tuple[set[str], set[str]]:
    text = p.read_text(encoding="utf-8")
    roles = set(re.findall(r"roles\s*:=\s*\{([^}]+)\}", text))
    actions = set(re.findall(r"actions\s*:=\s*\{([^}]+)\}", text))

    def _split(s: set[str]) -> set[str]:
        out: set[str] = set()
        for block in s:
            for tok in block.split(','):
                name = tok.strip().strip('"')
                if name:
                    out.add(name)
        return out

    return _split(roles), _split(actions)


def _run_gate(payload: dict[str, Any], env: dict[str, str] | None = None) -> int:
    e = os.environ.copy()
    e.update(env or {})
    proc = subprocess.run(
        ["python", "scripts/gates/roles_policy_gate.py"],
        input=json.dumps(payload),
        text=True,
        capture_output=True,
        env=e,
    )
    return proc.returncode


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pack", default=str(_repo() / "policies/governance/governance_pack.v0.1.yaml"))
    ap.add_argument("--rego", default=str(_repo() / "policies/security/roles.rego"))
    args = ap.parse_args()

    pack = _load_pack(Path(args.pack))
    doms = pack.get("domains") or {}
    roles_pack = set(map(str, pack.get("roles") or []))
    actions_pack = set(map(str, pack.get("actions") or []))

    roles_rego, actions_rego = _parse_rego_sets(Path(args.rego))

    missing_roles = roles_pack - roles_rego
    missing_actions = actions_pack - actions_rego
    if missing_roles or missing_actions:
        msg = (
            "Mismatch sets: "
            f"missing roles in rego={sorted(missing_roles)}, "
            f"missing actions in rego={sorted(missing_actions)}"
        )
        print(msg)
        return 1

    # Behavioral check via gate (lex domain by default)
    for dom, cfg in doms.items():
        allow = (cfg or {}).get("allow") or {}
        for action, allowed_list in allow.items():
            allowed = set(map(str, allowed_list or []))
            # pick a resource kind heuristic
            rkind = "keys" if action == "manage_keys" else ("policy" if action in {"merge", "manage_policy"} else "pco")
            for role in roles_pack:
                payload = {"user": {"role": role}, "action": action, "resource": {"kind": rkind, "scope": dom}}
                rc = _run_gate(payload)
                if (rc == 0) != (role in allowed):
                    exp = "ALLOW" if role in allowed else "DENY"
                    print(f"Gate mismatch: dom={dom} action={action} role={role} expected={exp} rc={rc}")
                    return 2
    print("Governance consistency: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
