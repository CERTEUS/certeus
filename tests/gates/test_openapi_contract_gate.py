#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_openapi_contract_gate.py             |
# | ROLE: Project test module.                                  |
# | PLIK: tests/gates/test_openapi_contract_gate.py             |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Smoke test bramki kontraktu OpenAPI: uruchomienie funkcji `check()` zwraca
    listy (violations, warnings) i nie podnosi wyjątków.

EN: Smoke test for OpenAPI contract gate: running `check()` returns lists
    (violations, warnings) without raising exceptions.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from scripts.gates.openapi_contract_gate import check

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===


def test_openapi_contract_gate_runs() -> None:
    vio, warn = check()
    assert isinstance(vio, list)
    assert isinstance(warn, list)
