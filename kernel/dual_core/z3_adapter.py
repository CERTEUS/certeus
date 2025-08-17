#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/kernel/dual_core/z3_adapter.py          |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

"""
PL: Adapter dla Z3 i zależności SMT.
EN: Adapter for Z3 and SMT.
"""

from __future__ import annotations

import logging
from typing import Any, Dict, List, cast

import z3  # type: ignore[reportMissingTypeStubs]
from kernel.smt_translator import (
    compile_bool_ast,
    validate_ast,
)  # <- wszystkie importy nad kodem

_Z3 = cast(Any, z3)
logger = logging.getLogger(__name__)


def compile_from_ast(ast_root: Any, *, validate: bool = True) -> z3.ExprRef:
    """
    PL: Kompiluje AST do formuły Z3 bez eval().
    EN: Compile AST to Z3 formula without eval().
    Zwraca ExprRef (BoolRef dziedziczy po ExprRef w naszych stubach).
    """
    if validate:
        validate_ast(cast(Any, ast_root))
    expr, symbols = compile_bool_ast(
        cast(Any, ast_root), declare_on_use=True, validate=False
    )
    logger.debug("Z3 adapter compiled expr with symbols: %s", list(symbols.keys()))
    return expr


class Z3Adapter:
    """
    Minimalny adapter wykonawczy dla Core-1:
    - solve(assertions): odpala solver Z3 i zwraca ujednolicony dict wyniku.
    """

    def solve(self, assertions: List["z3.ExprRef"]) -> Dict[str, Any]:
        s = z3.Solver()
        for a in assertions:
            s.add(a)
        status = s.check()
        result: Dict[str, Any] = {
            "status": str(status).lower(),  # "sat" / "unsat" / "unknown"
            "time_ms": None,
            "model": None,
            "error": None,
            "version": z3.get_version_string()
            if hasattr(z3, "get_version_string")
            else None,
        }
        try:
            if status == z3.sat:
                m = s.model()
                model_bindings = {d.name(): str(m[d]) for d in m.decls()}
                result["model"] = model_bindings
        except Exception as e:  # best-effort
            logger.exception("Model extraction failed: %s", e)
            result["error"] = f"model_error: {e}"
        return result
