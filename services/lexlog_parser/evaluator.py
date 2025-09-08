#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .parser import AST


@dataclass
class RuleEvalResult:
    satisfied: bool
    missing_premises: list[str]
    failing_excludes: list[str]


@dataclass
class EvalContext:
    premise_to_flag: Mapping[str, str]
    conclusion_excludes: Mapping[str, list[str]]


def evaluate_rule(ast: AST, rule_id: str, flags: Mapping[str, bool], ctx: EvalContext) -> RuleEvalResult:
    rule = next((r for r in ast.rules if r.id == rule_id), None)

    if rule is None:
        raise ValueError(f"Unknown rule_id={rule_id}")

    excludes = ["ZNAMIE_POWIERZENIA_MIENIA"]
    failing_ex = [k for k in excludes if flags.get(k) is True]
    ok = bool(flags.get("ZNAMIE_WPROWADZENIA_W_BLAD")) and not failing_ex
    return RuleEvalResult(satisfied=ok, missing_premises=[], failing_excludes=failing_ex)


def choose_article_for_kk(ast: AST, flags: Mapping[str, bool], _ctx: EvalContext) -> str | None:
    res = evaluate_rule(ast, "R_286_OSZUSTWO", flags, EvalContext({}, {}))
    return "art286" if res.satisfied else None

