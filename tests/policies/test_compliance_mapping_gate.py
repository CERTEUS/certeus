#!/usr/bin/env python3

"""
PL: Test smoke bramki mapowania zgodności (DPIA/ISO/SOC2).
EN: Smoke test for compliance mapping gate (DPIA/ISO/SOC2).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from scripts.gates.compliance_mapping_gate import check


def test_compliance_mapping_gate_runs() -> None:
    violations, warnings = check()
    assert isinstance(violations, list)
    assert isinstance(warnings, list)
