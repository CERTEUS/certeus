# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/services/test_lexlog_eval.py      |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |                   LEXLOG Evaluator Tests                    |
# +-------------------------------------------------------------+

"""
PL: Testy ewaluatora LEXLOG (MVP) dla art. 286 k.k., z loaderem mapowania.
EN: LEXLOG evaluator tests (MVP) for art. 286 PC, with mapping loader.
"""

from __future__ import annotations

from pathlib import Path

from services.lexlog_parser.evaluator import choose_article_for_kk, evaluate_rule
from services.lexlog_parser.mapping import load_mapping
from services.lexlog_parser.parser import parse_lexlog


def _load_kk_ast():
    lex_path = Path("packs") / "jurisdictions" / "PL" / "rules" / "kk.lex"
    content = lex_path.read_text(encoding="utf-8")
    return parse_lexlog(content)


def _load_ctx():
    map_path = Path("packs") / "jurisdictions" / "PL" / "rules" / "kk.mapping.json"
    assert map_path.exists(), "Missing kk.mapping.json"
    return load_mapping(map_path)


def test_286_passes_when_wprowadzenie_true_and_excludes_false() -> None:
    ast = _load_kk_ast()
    ctx = _load_ctx()

    flags = {
        "ZNAMIE_WPROWADZENIA_W_BLAD": True,
        "ZNAMIE_POWIERZENIA_MIENIA": False,
    }
    res = evaluate_rule(ast, "R_286_OSZUSTWO", flags, ctx)
    assert res.satisfied is True
    assert res.missing_premises == []
    assert res.failing_excludes == []
    assert choose_article_for_kk(ast, flags, ctx) == "art286"


def test_286_fails_when_excluded_flag_set() -> None:
    ast = _load_kk_ast()
    ctx = _load_ctx()

    flags = {
        "ZNAMIE_WPROWADZENIA_W_BLAD": True,
        "ZNAMIE_POWIERZENIA_MIENIA": True,  # exclude -> blokuje
    }
    res = evaluate_rule(ast, "R_286_OSZUSTWO", flags, ctx)
    assert res.satisfied is False
    assert res.failing_excludes == ["ZNAMIE_POWIERZENIA_MIENIA"]
    assert choose_article_for_kk(ast, flags, ctx) is None
