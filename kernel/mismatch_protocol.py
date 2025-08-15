# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: kernel/mismatch_protocol.py                           |
# | ROLE: Handles solver-result discrepancies (Dual-Core).      |
# | PLIK: kernel/mismatch_protocol.py                           |
# | ROLA: Obsługa rozbieżności wyników solverów (Dual-Core).    |
# +-------------------------------------------------------------+
"""
PL: Protokół zgłaszania rozbieżności między rdzeniami SMT.
EN: Protocol for reporting discrepancies between SMT cores.
"""

from typing import Dict, Any


class MismatchError(Exception):
    """PL: Rozbieżność wyników solverów. EN: Solver result mismatch."""


def handle_mismatch(formula_str: str, results: Dict[str, Dict[str, Any]]) -> None:
    """
    PL: Sygnalizuje rozjazd rdzeni (HITL w przyszłości).
    EN: Signals core disagreement (HITL hooks planned).
    """
    details: Dict[str, Any] = {
        "requires_human": True,
        "formula_preview": formula_str[:500],
        "results": {k: {"status": v.get("status", "n/a")} for k, v in results.items()},
    }
    raise MismatchError(f"Solver mismatch; details={details}")
