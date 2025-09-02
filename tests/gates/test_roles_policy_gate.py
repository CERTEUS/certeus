from __future__ import annotations

import subprocess


def run_gate(payload: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python", "scripts/gates/roles_policy_gate.py"],
        input=payload,
        text=True,
        capture_output=True,
    )


def test_roles_allow_publish_afv() -> None:
    payload = '{"user":{"role":"AFV"},"action":"publish","resource":{"kind":"pco","case_id":"CER-1"}}'
    res = run_gate(payload)
    assert res.returncode == 0, res.stderr or res.stdout
    assert "OK" in (res.stdout + res.stderr)


def test_roles_deny_manage_keys_by_atc() -> None:
    payload = '{"user":{"role":"ATC"},"action":"manage_keys","resource":{"kind":"keys"}}'
    res = run_gate(payload)
    assert res.returncode != 0
    assert "not permitted" in (res.stdout + res.stderr)
