#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: kernel/truth_engine.py                              |

# | ROLE: Project module.                                       |

# | PLIK: kernel/truth_engine.py                              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Moduł systemu CERTEUS.

EN: CERTEUS system module.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import time
from typing import Any, Protocol, cast

import z3  # type: ignore[reportMissingTypeStubs]

from .mismatch_protocol import handle_mismatch  # ✅ import at top to avoid E402

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
class _Z3AdapterProto(Protocol):
    def solve(self, assertions: list[z3.ExprRef]) -> dict[str, Any]: ...


class DualCoreVerifier:
    """Dual-Core verifier: Core-1(Z3) + Core-2(stub)."""

    def __init__(self) -> None:
        # ✅ unikamy konfliktu typów klas; instancja spełnia Protocol

        self.z3_adapter: _Z3AdapterProto = cast(_Z3AdapterProto, _AdapterClass())

    def _parse_smt2(self, smt2: str) -> list[Any]:
        assertions: Any = _Z3.parse_smt2_string(smt2)

        return [assertions[i] for i in range(len(assertions))]

    def _solve_core2_stub(self, core1_result: dict[str, Any], *, force_mismatch: bool) -> dict[str, Any]:
        r = dict(core1_result)

        if force_mismatch:
            if r.get("status") == "sat":
                r["status"] = "unsat"

            elif r.get("status") == "unsat":
                r["status"] = "sat"

            else:
                r["status"] = "unknown"

        return r

    def verify(
        self,
        formula: str,
        *,
        lang: str = "smt2",
        case_id: str | None = None,
        force_mismatch: bool = False,
    ) -> dict[str, Any]:
        if lang != "smt2":
            raise ValueError("Only 'smt2' formulas are accepted in this MVP.")

        assertions = self._parse_smt2(formula)

        # Core-1

        result_z3 = self.z3_adapter.solve(assertions)

        status_norm = (result_z3.get("status") or "").lower()

        if status_norm in {"sat", "unsat", "unknown"}:
            result_z3["status"] = status_norm

        # Core-2

        result_core2 = self._solve_core2_stub(result_z3, force_mismatch=force_mismatch)

        # Divergence?

        if (result_z3.get("status") or "").lower() != (result_core2.get("status") or "").lower():
            handle_mismatch(
                case_id=case_id or "temp-case-id",
                formula_str=formula,
                results={"z3": result_z3, "cvc5_stub": result_core2},
            )

        return result_z3


# === LOGIKA / LOGIC ===


_Z3 = cast(Any, z3)


# Import adapter class if dostępny; w przeciwnym razie fallback.

try:
    from .dual_core.z3_adapter import Z3Adapter as _AdapterClass  # type: ignore[assignment]

except Exception:

    class _AdapterClass:  # type: ignore[no-redef]
        """Fallback adapter: solves a list of Z3 assertions with Z3.Solver()."""

        def solve(self, assertions: list[z3.ExprRef]) -> dict[str, Any]:
            start = time.perf_counter()

            s = z3.Solver()

            for a in assertions:
                s.add(a)

            status = s.check()

            elapsed = (time.perf_counter() - start) * 1000.0

            result: dict[str, Any] = {
                "status": str(status).lower(),  # "sat" / "unsat" / "unknown"
                "time_ms": round(elapsed, 3),
                "model": None,
                "error": None,
                "version": z3.get_version_string() if hasattr(z3, "get_version_string") else None,
            }

            if status == z3.sat:
                m = s.model()

                try:
                    model_bindings = {d.name(): str(m[d]) for d in m.decls()}

                except Exception:
                    model_bindings = {}

                result["model"] = model_bindings

            return result


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
