# pyright: reportMissingTypeStubs=false
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: kernel/truth_engine.py                                |
# | ROLE: Truth Engine orchestrating Dual-Core verification.    |
# | PLIK: kernel/truth_engine.py                                |
# | ROLA: Silnik Prawdy orkiestrujący weryfikację Dual-Core.    |
# +-------------------------------------------------------------+
"""
PL: Weryfikator SMT (MVP: SMT-LIB2) uruchamiający Z3. Drugi rdzeń = stub.
EN: SMT verifier (MVP: SMT-LIB2) running Z3. Second core = stub.
"""

# === IMPORTY / IMPORTS ======================================== #
from typing import Any, Dict, List, cast
import z3
from .dual_core.z3_adapter import Z3Adapter
from .mismatch_protocol import handle_mismatch

# Uspokojenie Pylance (z3 bez stubów typów)
_z3 = cast(Any, z3)


# === WERYFIKATOR / VERIFIER =================================== #
class DualCoreVerifier:
    """
    PL: Weryfikator w architekturze Dual-Core (drugi rdzeń dołączymy później).
    EN: Verifier in Dual-Core architecture (second core to be added later).
    """

    # --- INIT / KONSTRUKTOR ----------------------------------- #
    def __init__(self) -> None:
        self.z3_adapter = Z3Adapter()

    # --- PARSER SMT-LIB2 -------------------------------------- #
    def _parse_smt2(self, smt2: str) -> List[Any]:
        """
        PL: Parsuje SMT-LIB2 do listy asercji Z3.
        EN: Parses SMT-LIB2 into a list of Z3 assertions.
        """
        assertions: Any = _z3.parse_smt2_string(smt2)
        return [assertions[i] for i in range(len(assertions))]

    # --- WERYFIKACJA ------------------------------------------ #
    def verify(self, formula: str, lang: str = "smt2") -> Dict[str, Any]:
        """
        PL: Weryfikuje formułę; MVP obsługuje tylko 'smt2'.
        EN: Verifies a formula; MVP supports 'smt2' only.
        """
        if lang != "smt2":
            raise ValueError("Only 'smt2' formulas are accepted in this MVP.")

        assertions = self._parse_smt2(formula)
        result_z3 = self.z3_adapter.solve(assertions)

        # Stub drugiego rdzenia – na razie kopiujemy wynik Z3
        result_cvc5_stub = result_z3

        if result_z3.get("status") != result_cvc5_stub.get("status"):
            handle_mismatch(
                formula_str=formula,
                results={"z3": result_z3, "cvc5_stub": result_cvc5_stub},
            )
        return result_z3
