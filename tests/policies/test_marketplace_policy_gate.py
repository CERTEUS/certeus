#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/policies/test_marketplace_policy_gate.py        |
# | ROLE: Project test module.                                  |
# | PLIK: tests/policies/test_marketplace_policy_gate.py        |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Test smoke dla bramki Marketplace Policy — ma się wykonać bez wyjątku
    i zwrócić krotkę (violations, warnings).

EN: Smoke test for Marketplace Policy gate — should run without exceptions
    and return a tuple (violations, warnings).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from scripts.gates.marketplace_policy_gate import check


def test_marketplace_policy_gate_runs() -> None:
    violations, warnings = check()
    assert isinstance(violations, list)
    assert isinstance(warnings, list)
