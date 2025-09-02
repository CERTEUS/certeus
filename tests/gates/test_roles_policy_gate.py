"""
PL: Testy bramki ról: pozytywne (AFV publish) i negatywne (ATC manage_keys).
EN: Roles gate tests: positive (AFV publish) and negative (ATC manage_keys).
"""

from __future__ import annotations

import subprocess  # noqa: E402

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_roles_policy_gate.py                |
# | ROLE: Tests for Roles Policy gate                            |
# | PLIK: tests/gates/test_roles_policy_gate.py                |
# | ROLA: Testy bramki ról                                       |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===

# === LOGIKA / LOGIC ===


def run_gate(payload: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python", "scripts/gates/roles_policy_gate.py"],
        input=payload,
        text=True,
        capture_output=True,
    )


# === TESTY / TESTS ===


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
