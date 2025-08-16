# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |      Core Engine for Reliable & Unified Systems             |
# +-------------------------------------------------------------+
# | FILE: services/lexlog_parser/parser.py                      |
# | ROLE: Minimal, tolerant LEXLOG parser (stub) producing AST. |
# +-------------------------------------------------------------+

"""
PL: Minimalny parser LEXLOG (MVP). Parsuje DEFINE/PREMISE/RULE/CONCLUSION
    przy uzyciu prostych regexow i zwraca AST jako Pydantic DTO.
EN: Minimal LEXLOG parser (MVP). Parses DEFINE/PREMISE/RULE/CONCLUSION
    using simple regex and returns AST as Pydantic DTOs.
"""

from __future__ import annotations

import re
from pydantic import BaseModel, Field


class DefineItem(BaseModel):
    """PL: Definicja zmiennej logicznej. EN: Logical variable definition."""

    name: str = Field(...)
    type: str = Field(...)


class PremiseItem(BaseModel):
    """PL: Przeslanka z ID i etykieta. EN: Premise with ID and label."""

    id: str = Field(...)
    label: str = Field(...)


class RuleItem(BaseModel):
    """PL: Regula wiaze przeslanki z konkluzja. EN: Rule ties premises to conclusion."""

    id: str = Field(...)
    premises: list[str] = Field(default_factory=list)
    conclusion: str = Field(...)


class ConclusionItem(BaseModel):
    """PL: Konkluzja z opcjonalnym wyrazeniem ASSERT. EN: Conclusion with optional ASSERT."""

    id: str = Field(...)
    label: str = Field(...)
    assert_expr: str | None = Field(default=None)


# --- Typed default factories (uciszaja Pylance) ---
def _empty_defines() -> list[DefineItem]:
    return []


def _empty_premises() -> list[PremiseItem]:
    return []


def _empty_rules() -> list[RuleItem]:
    return []


def _empty_conclusions() -> list[ConclusionItem]:
    return []


class LexAst(BaseModel):
    """PL: Drzewo LEXLOG. EN: LEXLOG AST."""

    defines: list[DefineItem] = Field(default_factory=_empty_defines)
    premises: list[PremiseItem] = Field(default_factory=_empty_premises)
    rules: list[RuleItem] = Field(default_factory=_empty_rules)
    conclusions: list[ConclusionItem] = Field(default_factory=_empty_conclusions)


# Regex (ASCII-friendly)
_RE_COMMENT = re.compile(r"^\s*#")
_RE_BLANK = re.compile(r"^\s*$")
_RE_DEFINE = re.compile(r"^\s*DEFINE\s+([A-Za-z0-9_]+)\s*:\s*([A-Za-z0-9_]+)\s*$")
_RE_PREMISE = re.compile(r'^\s*PREMISE\s+([A-Za-z0-9_]+)\s*:\s*"([^"]+)"\s*$')
_RE_RULE = re.compile(
    r"^\s*RULE\s+([A-Za-z0-9_]+)\s*\(\s*([A-Za-z0-9_,\s]*)\s*\)\s*->\s*([A-Za-z0-9_]+)\s*$"
)
_RE_CONCLUSION = re.compile(r'^\s*CONCLUSION\s+([A-Za-z0-9_]+)\s*:\s*"([^"]+)"\s*$')
_RE_ASSERT = re.compile(r"^\s*ASSERT\s*\(\s*(.+)\s*\)\s*$")


def parse_lexlog(text: str) -> LexAst:
    """
    PL: Parsuje tresc LEXLOG do AST. Niezrozumiale linie ignoruje (MVP).
    EN: Parses LEXLOG content into AST. Unknown lines are ignored (MVP).
    """
    ast = LexAst()
    current_conclusion: ConclusionItem | None = None

    for raw in text.splitlines():
        line = raw.rstrip("\n")

        if _RE_BLANK.match(line) or _RE_COMMENT.match(line):
            continue

        m = _RE_DEFINE.match(line)
        if m:
            ast.defines.append(DefineItem(name=m.group(1), type=m.group(2)))
            continue

        m = _RE_PREMISE.match(line)
        if m:
            ast.premises.append(PremiseItem(id=m.group(1), label=m.group(2)))
            continue

        m = _RE_RULE.match(line)
        if m:
            rid = m.group(1)
            plist_raw = m.group(2).strip()
            prem_list = [p.strip() for p in plist_raw.split(",")] if plist_raw else []
            ast.rules.append(
                RuleItem(
                    id=rid, premises=[p for p in prem_list if p], conclusion=m.group(3)
                )
            )
            continue

        m = _RE_CONCLUSION.match(line)
        if m:
            current_conclusion = ConclusionItem(id=m.group(1), label=m.group(2))
            ast.conclusions.append(current_conclusion)
            continue

        m = _RE_ASSERT.match(line)
        if m and current_conclusion is not None:
            current_conclusion.assert_expr = m.group(1)
            continue

        # Unknown line -> ignore (MVP)

    return ast
