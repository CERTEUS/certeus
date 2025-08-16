# +-------------------------------------------------------------+
# |               CERTEUS - DualCore Verifier (MVP)             |
# +-------------------------------------------------------------+
# | FILE: kernel/e2e_verifier.py                                |
# | ROLE: Minimal verifier using Z3 and SMTTranslator.          |
# | PLIK: kernel/e2e_verifier.py                                |
# | ROLA: Minimalny weryfikator Z3 z użyciem SMTTranslator.     |
# +-------------------------------------------------------------+

# pyright: reportMissingTypeStubs=false, reportUnknownMemberType=false

"""
PL: Minimalny weryfikator E2E oparty o Z3. Przyjmuje fakty i regułę LEXLOG
    (parsowaną wcześniej), buduje formułę przez SMTTranslator i rozwiązuje.
EN: Minimal end-to-end verifier based on Z3. Takes facts and a parsed LEXLOG
    rule, builds a formula via SMTTranslator, and solves it.
"""

# [BLOCK: IMPORTS]
from __future__ import annotations

from typing import Any, Dict, Iterable, Mapping

import z3  # z3-solver nie ma stubów typów -> patrz dyrektywa pyright wyżej

from .smt_translator import SMTTranslator


# [BLOCK: CLASS • DualCoreVerifier]
class DualCoreVerifier:
    """
    PL: Minimalny adapter do solvera Z3; reprezentuje „rdzeń” weryfikatora.
    EN: Minimal adapter to the Z3 solver; represents the verifier 'core'.
    """

    def __init__(self) -> None:
        self.translator = SMTTranslator()

    def analyze_case(
        self, facts: Iterable[Any], parsed_rule: Mapping[str, Any]
    ) -> Dict[str, Any]:
        """
        PL: Tłumaczy fakty + regułę na formułę i rozwiązuje w Z3.
        EN: Translates facts + rule to a formula and solves it in Z3.
        """
        # [BLOCK: TRANSLATE]
        formula: Any = self.translator.translate_to_formula(facts, parsed_rule)

        # [BLOCK: SOLVE]
        solver: Any = z3.Solver()
        solver.add(formula)
        status: Any = solver.check()

        # [BLOCK: RESULT PACK]
        res: Dict[str, Any] = {"status": str(status)}
        if status == z3.sat:
            model: Any = solver.model()
            model_map: Dict[str, str] = {}
            # model.decls() -> iterable deklaracji; brak stubów → Any
            for d in model.decls():  # type: ignore[reportUnknownVariableType]
                # d.name() to API Z3: nazwa symbolu; brak stubów → Any
                model_map[str(d.name())] = str(model[d])  # type: ignore[index]
            res["model"] = model_map

        return res
