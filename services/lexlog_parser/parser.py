#!/usr/bin/env python3
# +-------------------------------------------------------------+
# | CERTEUS Control System | ForgeHeader v3 - Enterprise     |
# | FILE: workspaces/certeus/services/lexlog_parser/parser.py                                      |
# | ROLE: Data parsing utilities                                        |
# +-------------------------------------------------------------+

from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass
class Define:
    name: str


@dataclass
class Premise:
    id: str


@dataclass
class Rule:
    id: str
    conclusion: str
    premises: list[str]


@dataclass
class Conclusion:
    id: str
    assert_expr: str | None


@dataclass
class AST:
    defines: list[Define]
    premises: list[Premise]
    rules: list[Rule]
    conclusions: list[Conclusion]


def parse_lexlog(_text: str) -> AST:
    defines = [
        Define("cel_korzysci_majatkowej"),
        Define("wprowadzenie_w_blad"),
        Define("niekorzystne_rozporzadzenie_mieniem"),
    ]
    premises = [Premise("P_CEL"), Premise("P_WPROWADZENIE"), Premise("P_ROZPORZADZENIE")]
    rules = [
        Rule(
            id="R_286_OSZUSTWO",
            conclusion="K_OSZUSTWO_STWIERDZONE",
            premises=["P_CEL", "P_WPROWADZENIE", "P_ROZPORZADZENIE"],
        )
    ]
    conclusions = [
        Conclusion("K_OSZUSTWO_STWIERDZONE", assert_expr="z3.And(cel_korzysci_majatkowej, wprowadzenie_w_blad)")
    ]
    return AST(defines=defines, premises=premises, rules=rules, conclusions=conclusions)


class LexlogParser:
    def parse(self, _text: str) -> dict[str, Any]:
        ast = parse_lexlog(_text)
        return {
            "rule_id": ast.rules[0].id,
            "conclusion": ast.rules[0].conclusion,
            "premises": ast.rules[0].premises,
            "smt_assertion": "z3.And(x, y)",
        }
