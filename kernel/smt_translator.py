# +-------------------------------------------------------------+
# |                CERTEUS - SMT Translator (MVP)               |
# +-------------------------------------------------------------+
# | FILE: kernel/smt_translator.py                              |
# | ROLE: Translate high-level facts & parsed rules to Z3 SMT.  |
# | PLIK: kernel/smt_translator.py                              |
# | ROLA: Tłumaczenie faktów i reguł LEXLOG na formuły Z3.      |
# +-------------------------------------------------------------+

# pyright: reportMissingTypeStubs=false, reportUnknownMemberType=false

"""
PL: Translator SMT: tłumaczy fakty domenowe i regułę LEXLOG na formułę Z3.
EN: SMT translator: converts domain facts and a LEXLOG rule into a Z3 formula.
"""

# [BLOCK: IMPORTS]
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Mapping, TypedDict, cast

import z3  # brak stubów typów – patrz dyrektywa pyright wyżej


# [BLOCK: TYPES]
class FactMapping(TypedDict, total=False):
    """PL: Ogólny kształt mapowanego faktu (MVP).
    EN: General shape of mapped fact (MVP)."""

    role: str
    value: Any


class FactMappingWithRole(TypedDict):
    """PL: Mapowany fakt z wymaganym kluczem 'role'.
    EN: Mapped fact with required 'role' key."""

    role: str
    value: Any | None


@dataclass(frozen=True)
class SimpleFact:
    """PL: Minimalny fakt domenowy. EN: Minimal domain fact."""

    role: str
    value: Any | None = None


# [BLOCK: CLASS • SMTTranslator]
class SMTTranslator:
    """
    PL: Buduje formułę Z3 na podstawie faktów i reguły (string asercji SMT).
    EN: Builds a Z3 formula based on facts and a rule (SMT assertion string).
    """

    # [BLOCK: UTIL • normalize facts]
    def _normalize_facts(self, facts: Iterable[Any]) -> List[SimpleFact]:
        """
        Akceptuje:
        - SimpleFact,
        - Mapping zgodny z FactMapping (ma klucz 'role', opcjonalnie 'value').
        Zwraca listę SimpleFact.
        """
        norm: List[SimpleFact] = []
        for f in facts:
            if isinstance(f, SimpleFact):
                norm.append(f)
            elif isinstance(f, Mapping) and "role" in f:
                # Po sprawdzeniu obecności 'role' bezpiecznie rzutujemy:
                fm: FactMappingWithRole = cast(FactMappingWithRole, f)
                role_val: str = fm["role"]
                value_val: Any | None = fm.get("value")
                norm.append(SimpleFact(role=role_val, value=value_val))
            # inne kształty – ignorujemy w MVP
        return norm

    # [BLOCK: API • translate_to_formula]
    def translate_to_formula(
        self, facts: Iterable[Any], parsed_rule: Mapping[str, Any]
    ) -> Any:
        """
        Zwraca obiekt BoolRef Z3 (typ Any: brak stubów) będący koniunkcją:
        (asercje z faktów) ∧ (asercja reguły z parsed_rule['smt_assertion']).
        """
        facts_n: List[SimpleFact] = self._normalize_facts(facts)

        # [BLOCK: VARS] – zmienne Boole dla art. 286 (MVP)
        cel_korzysci_majatkowej: Any = z3.Bool("cel_korzysci_majatkowej")
        wprowadzenie_w_blad: Any = z3.Bool("wprowadzenie_w_blad")
        niekorzystne_rozporzadzenie_mieniem: Any = z3.Bool(
            "niekorzystne_rozporzadzenie_mieniem"
        )

        # [BLOCK: FACT ASSERTIONS]
        fact_assertions: List[Any] = []
        for fact in facts_n:
            if fact.role == "intent_financial_gain":
                fact_assertions.append(cel_korzysci_majatkowej == z3.BoolVal(True))
            elif fact.role == "act_deception":
                fact_assertions.append(wprowadzenie_w_blad == z3.BoolVal(True))
            elif fact.role == "detrimental_property_disposal":
                fact_assertions.append(
                    niekorzystne_rozporzadzenie_mieniem == z3.BoolVal(True)
                )

        # [BLOCK: RULE ASSERTION]
        rule_assertion_str: str = str(
            parsed_rule.get("smt_assertion", "z3.BoolVal(True)")
        )
        # UWAGA: eval() tylko w kontrolowanym środowisku (MVP).
        safe_env: Dict[str, Any] = {
            "z3": z3,
            "Bool": z3.Bool,
            "And": z3.And,
            "Or": z3.Or,
            "Not": z3.Not,
            "BoolVal": z3.BoolVal,
            "cel_korzysci_majatkowej": cel_korzysci_majatkowej,
            "wprowadzenie_w_blad": wprowadzenie_w_blad,
            "niekorzystne_rozporzadzenie_mieniem": niekorzystne_rozporzadzenie_mieniem,
        }
        rule_assertion: Any = eval(rule_assertion_str, safe_env)  # noqa: S307 – MVP, sandboxed env

        # [BLOCK: COMBINE]
        if fact_assertions:
            # Z3 nie ma stubów typów → jawnie rzutujemy wynik And(...) na Any
            final_formula = cast(Any, z3.And(z3.And(*fact_assertions), rule_assertion))
            return final_formula
        return rule_assertion
