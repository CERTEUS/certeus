# pyright: reportMissingTypeStubs=false
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: kernel/dual_core/z3_adapter.py                        |
# | ROLE: Z3 SMT adapter with proofs & unsat-core enabled.      |
# | PLIK: kernel/dual_core/z3_adapter.py                        |
# | ROLA: Adapter Z3 z włączonymi proof/unsat-core.             |
# +-------------------------------------------------------------+
"""
PL: Adapter Z3 zwracający status i artefakty (model/proof/unsat_core).
EN: Z3 adapter returning status and artifacts (model/proof/unsat_core).
"""

# === IMPORTY / IMPORTS ======================================== #
from typing import Any, Dict, List, cast
import z3  # wymaga: pip install z3-solver

# Uspokojenie Pylance (z3 nie ma stubów typów)
_z3 = cast(Any, z3)


# === ADAPTER / ADAPTER ======================================== #
class Z3Adapter:
    """
    PL: Adapter uruchamiający solver Z3 dla listy asercji.
    EN: Adapter that runs Z3 solver for a list of assertions.
    """

    # --- INIT / KONSTRUKTOR ----------------------------------- #
    def __init__(self) -> None:
        # Włącz proofy globalnie (przydatne dla 'unsat')
        _z3.set_param(proof=True)

    # --- SOLVE ------------------------------------------------ #
    def solve(self, assertions: List[Any]) -> Dict[str, Any]:
        """
        PL: Uruchamia solver na asercjach i zwraca ustandaryzowany wynik.
        EN: Runs the solver on assertions and returns a standardized result.
        """
        s: Any = _z3.Solver()
        labels: List[Any] = [
            _z3.Bool(f"a{i}") for i, _ in enumerate(assertions, start=1)
        ]
        for a, lbl in zip(assertions, labels):
            s.assert_and_track(a, lbl)

        res: Any = s.check()
        if res == _z3.sat:
            return {"status": "sat", "model": str(s.model())}
        if res == _z3.unsat:
            core = [str(c) for c in s.unsat_core()]
            try:
                proof_str = str(s.proof())
            except Exception:
                proof_str = ""
            return {"status": "unsat", "unsat_core": core, "proof": proof_str}
        return {"status": "unknown", "reason": s.reason_unknown()}
