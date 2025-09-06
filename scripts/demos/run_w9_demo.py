#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w9_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w9_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W9 — Security hardening: uruchom role gate, bunker gate i PQ‑crypto gate
    w trybie demonstracyjnym i zapisz raport.

EN: W9 — Security hardening: run roles gate, bunker gate and PQ‑crypto gate in
    demo mode and save a report.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess


def _run(cmd: list[str], *, input_json: dict | None = None, env: dict[str, str] | None = None) -> tuple[int, str, str]:
    e = os.environ.copy()
    if env:
        e.update(env)
    in_bytes = None
    if input_json is not None:
        in_bytes = json.dumps(input_json).encode("utf-8")
    p = subprocess.run(cmd, input=in_bytes, capture_output=True, env=e)
    return (
        p.returncode,
        (p.stdout or b"").decode("utf-8", errors="ignore"),
        (p.stderr or b"").decode("utf-8", errors="ignore"),
    )


def main() -> int:
    out_dir = Path("reports")
    out_dir.mkdir(parents=True, exist_ok=True)
    rep: dict[str, object] = {}

    # Roles gate (expect OK for AFV publish)
    rc_roles_ok, out_roles_ok, _ = _run(
        ["python", "scripts/gates/roles_policy_gate.py"],
        input_json={
            "user": {"role": "AFV"},
            "action": "publish",
            "resource": {"kind": "pco", "scope": "lex"},
        },
    )
    # Roles gate (expect FAIL for unknown role)
    rc_roles_fail, out_roles_fail, _ = _run(
        ["python", "scripts/gates/roles_policy_gate.py"],
        input_json={
            "user": {"role": "XXX"},
            "action": "merge",
            "resource": {"kind": "pco", "scope": "lex"},
        },
    )
    rep["roles_gate"] = {
        "ok_rc": rc_roles_ok,
        "ok_out": out_roles_ok.strip(),
        "fail_rc": rc_roles_fail,
        "fail_out": out_roles_fail.strip(),
    }

    # Bunker gate (off)
    rc_bunker_off, out_bunker_off, _ = _run(["python", "scripts/gates/security_bunker_gate.py"], env={"BUNKER": "0"})
    # Bunker gate (on, with attestation)
    att = Path("out")
    att.mkdir(parents=True, exist_ok=True)
    att_file = att / "att.json"
    att_file.write_text("{}", encoding="utf-8")
    rc_bunker_on, out_bunker_on, _ = _run(
        ["python", "scripts/gates/security_bunker_gate.py"],
        env={"BUNKER": "1", "BUNKER_ATTESTATION_PATH": str(att_file)},
    )
    rep["bunker_gate"] = {
        "off_rc": rc_bunker_off,
        "off_out": out_bunker_off.strip(),
        "on_rc": rc_bunker_on,
        "on_out": out_bunker_on.strip(),
    }

    # PQ‑crypto gate (informational)
    rc_pq, out_pq, _ = _run(
        ["python", "scripts/gates/pqcrypto_gate.py"],
        env={"PQCRYPTO_REQUIRE": "1", "PQCRYPTO_READY": "1"},
    )
    rep["pqcrypto_gate"] = {"rc": rc_pq, "out": out_pq.strip()}

    (out_dir / "w9_demo.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(json.dumps({"ok": True, "roles": rc_roles_ok == 0, "bunker": rc_bunker_on == 0}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
