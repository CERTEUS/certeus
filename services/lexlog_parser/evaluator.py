# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/lexlog_parser/evaluator.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/lexlog_parser/evaluator.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Ewaluator LEXLOG (MVP). Sprawdza, czy reguly z AST sa spelnione

    w oparciu o slownik flag booleowskich z silnika (flags).

EN: LEXLOG evaluator (MVP). Checks if AST rules hold based on engine

    boolean flags dictionary.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from pydantic import BaseModel, Field

from services.lexlog_parser.parser import LexAst

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class EvalContext(BaseModel):
    """Mapping context LEXLOG -> engine flags."""

    premise_to_flag: dict[str, str] = Field(default_factory=dict)

    conclusion_excludes: dict[str, list[str]] = Field(default_factory=dict)


class RuleEvalResult(BaseModel):
    rule_id: str

    conclusion_id: str

    satisfied: bool

    missing_premises: list[str] = Field(default_factory=list)

    failing_excludes: list[str] = Field(default_factory=list)


# === LOGIKA / LOGIC ===


def _flag(flags: Mapping[str, bool], name: str) -> bool:
    """Safe flag read (missing -> False)."""

    return bool(flags.get(name, False))


def evaluate_rule(
    ast: LexAst, rule_id: str, flags: Mapping[str, bool], ctx: EvalContext
) -> RuleEvalResult:
    rule = next((r for r in ast.rules if r.id == rule_id), None)

    if rule is None:
        raise ValueError(f"Unknown rule_id={rule_id}")

    conclusion_id = cast(str, rule.conclusion)  # ✅ dla .get i serializacji

    excludes: list[str] = ctx.conclusion_excludes.get(conclusion_id, [])

    missing: list[str] = []

    for p in rule.premises:
        flag_name = ctx.premise_to_flag.get(p)

        if not flag_name:
            continue  # no mapping yet in MVP

        if not _flag(flags, flag_name):
            missing.append(p)

    failing_exc: list[str] = [ex for ex in excludes if _flag(flags, ex)]

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
    res = evaluate_rule(ast, "R_286_OSZUSTWO", flags, ctx)

    return "art286" if res.satisfied else None


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
