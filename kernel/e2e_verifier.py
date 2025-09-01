#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: kernel/e2e_verifier.py                              |

# | ROLE: Project module.                                       |

# | PLIK: kernel/e2e_verifier.py                              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Weryfikator E2E przepływów CERTEUS.

EN: E2E verifier for CERTEUS flows.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import logging
from typing import Any, cast

import z3  # type: ignore[reportMissingTypeStubs]

from .smt_translator import compile_bool_ast, validate_ast

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
class E2EVerifier:
    """

    PL: Prosty weryfikator E2E:

        - verify_ast: kompiluje AST do Z3 i rozwiązuje.

        - verify_smt2: parsuje SMT-LIB2 i rozwiązuje.

    EN: Simple E2E verifier:

        - verify_ast: compile boolean AST to Z3 and solve.

        - verify_smt2: parse SMT-LIB2 and solve.

    """

    def __init__(self) -> None:
        # use runtime-selected adapter without static class-name conflicts

        self.z3: Any = _AdapterClass()

    # ──────────────────────────────────────────────────────────────────

    # AST → Z3

    # ──────────────────────────────────────────────────────────────────

    def compile_ast_to_z3(self, ast_root: Any, *, do_validate: bool = True) -> z3.ExprRef:
        """

        Compile CERTEUS boolean AST to a single Z3 expression.

        """

        if do_validate:
            validate_ast(cast(Any, ast_root))

        expr, _symbols = compile_bool_ast(cast(Any, ast_root), declare_on_use=True, validate=False)

        return expr  # ExprRef (BoolRef derives from ExprRef in stubs)

    def verify_ast(self, ast_root: Any, *, do_validate: bool = True) -> dict[str, Any]:
        """

        PL: Kompiluje AST do jednej formuły i rozwiązuje ją Z3.

        EN: Compile AST to a single assertion and solve it with Z3.

        """

        expr = self.compile_ast_to_z3(ast_root, do_validate=do_validate)

        return self.z3.solve([expr])

    # ──────────────────────────────────────────────────────────────────

    # SMT-LIB2 → Z3

    # ──────────────────────────────────────────────────────────────────

    def _parse_smt2_assertions(self, smt2: str) -> list[z3.ExprRef]:
        vec = z3.parse_smt2_string(smt2)

        return [vec[i] for i in range(len(vec))]

    def verify_smt2(self, smt2: str) -> dict[str, Any]:
        """

        PL: Parsuje SMT-LIB2, wysyła wszystkie asercje do solvera i zwraca wynik.

        EN: Parse SMT-LIB2, send all assertions to the solver and return the result.

        """

        assertions = self._parse_smt2_assertions(smt2)

        return self.z3.solve(assertions)


# === LOGIKA / LOGIC ===


logger = logging.getLogger(__name__)


# -----------------------------------------------------------------------------

# Adapter selection (no type redefinition conflicts for Pylance)

# -----------------------------------------------------------------------------

try:
    # Prefer project adapter; name kept distinct to avoid redefinition issues.

    from .dual_core.z3_adapter import Z3Adapter as _AdapterClass  # type: ignore[assignment]

except Exception:  # pragma: no cover - emergency fallback

    class _AdapterClass:  # type: ignore[no-redef]
        """Fallback adapter: solve a list of Z3 assertions with z3.Solver()."""

        def solve(self, assertions: list[z3.ExprRef]) -> dict[str, Any]:
            s = z3.Solver()

            for a in assertions:
                s.add(a)

            status = s.check()

            result: dict[str, Any] = {
                "status": str(status).lower(),
                "time_ms": None,
                "model": None,
                "error": None,
                "version": z3.get_version_string() if hasattr(z3, "get_version_string") else None,
            }

            if status == z3.sat:
                try:
                    m = s.model()

                    result["model"] = {d.name(): str(m[d]) for d in m.decls()}

                except Exception as e:  # best-effort
                    result["error"] = f"model_error: {e}"

            return result


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
