# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |      Core Engine for Reliable & Unified Systems             |
# +-------------------------------------------------------------+
# | FILE: services/lexlog_parser/evaluator.py                   |
# | ROLE: Evaluate LEXLOG AST against engine boolean flags.     |
# +-------------------------------------------------------------+

"""
PL: Ewaluator LEXLOG (MVP). Sprawdza, czy reguly z AST sa spelnione
    w oparciu o slownik flag booleowskich z silnika (flags).
EN: LEXLOG evaluator (MVP). Checks if AST rules hold based on engine
    boolean flags dictionary.
"""

from __future__ import annotations

from typing import Dict, List, Mapping
from pydantic import BaseModel, Field

from services.lexlog_parser.parser import LexAst


class EvalContext(BaseModel):
    """
    PL: Kontekst mapowania LEXLOG -> engine flags.
    EN: Mapping context LEXLOG -> engine flags.
    """

    premise_to_flag: Dict[str, str] = Field(default_factory=dict)
    conclusion_excludes: Dict[str, List[str]] = Field(default_factory=dict)


class RuleEvalResult(BaseModel):
    rule_id: str
    conclusion_id: str
    satisfied: bool
    missing_premises: List[str] = Field(default_factory=list)
    failing_excludes: List[str] = Field(default_factory=list)


def _flag(flags: Mapping[str, bool], name: str) -> bool:
    """Bezpieczny odczyt flagi (brak -> False)."""
    return bool(flags.get(name, False))


def evaluate_rule(
    ast: LexAst, rule_id: str, flags: Mapping[str, bool], ctx: EvalContext
) -> RuleEvalResult:
    """
    PL: Sprawdza pojedyncza regule z AST przeciwko slownikowi flags.
    EN: Checks a single AST rule against a flags dictionary.
    """
    rule = next((r for r in ast.rules if r.id == rule_id), None)
    if rule is None:
        raise ValueError(f"Unknown rule_id={rule_id}")

    conclusion_id = rule.conclusion
    excludes: List[str] = ctx.conclusion_excludes.get(conclusion_id, [])

    missing: List[str] = []
    for p in rule.premises:
        flag_name = ctx.premise_to_flag.get(p)
        if not flag_name:
            # Brak mapowania -> na MVP traktujemy jako „nie sprawdzamy”
            continue
        if not _flag(flags, flag_name):
            missing.append(p)

    failing_exc: List[str] = [ex for ex in excludes if _flag(flags, ex)]
    ok = not missing and not failing_exc

    return RuleEvalResult(
        rule_id=rule_id,
        conclusion_id=conclusion_id,
        satisfied=ok,
        missing_premises=missing,
        failing_excludes=failing_exc,
    )


def choose_article_for_kk(
    ast: LexAst, flags: Mapping[str, bool], ctx: EvalContext
) -> str | None:
    """
    PL: Minimalne rozstrzygniecie art. 286 (MVP).
        Jesli R_286_OSZUSTWO spelniona -> zwroc 'art286', wpp None.
    EN: Minimal decision for art. 286 (MVP).
        If R_286_OSZUSTWO satisfied -> return 'art286', else None.
    """
    res = evaluate_rule(ast, "R_286_OSZUSTWO", flags, ctx)
    return "art286" if res.satisfied else None
