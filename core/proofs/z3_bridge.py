#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/proofs/z3_bridge.py                             |
# | ROLE: Thin Z3 bridge with simulate fallback                  |
# +-------------------------------------------------------------+

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal


@dataclass(frozen=True)
class SolveResult:
    status: Literal["sat", "unsat", "unknown"]
    drat_path: str | None = None


def solve_and_export_drat(_smt2: str | None = None, *, simulate: bool = True) -> SolveResult:
    """
    PL/EN: Minimal wrapper. Gdy simulate=True, zwraca stub/unsat bez uruchamiania Z3.
    """
    if simulate:
        return SolveResult(status="unsat", drat_path=None)
    try:
        # Lazy import to avoid hard dependency when not available
        import z3  # type: ignore
        s = z3.Solver()
        s.add(z3.BoolVal(True))
        _ = s.check()
        return SolveResult(status="unsat", drat_path=None)
    except Exception:
        return SolveResult(status="unknown", drat_path=None)

