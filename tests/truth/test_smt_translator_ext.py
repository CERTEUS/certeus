#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/truth/test_smt_translator_ext.py  |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/truth/test_smt_translator_|
# | DATE:    2025-08-17                                          |
# +=====================================================================+
"""
PL: Testy jednostkowe / integracyjne modułu.
EN: Module test suite (unit/integration).
"""

# -*- coding: utf-8 -*-
# +=====================================================================+
# |                              CERTEUS                                |
# |                Tests — SMT Translator (extended)                    |
# +=====================================================================+
# | FILE:    tests/truth/test_smt_translator_ext.py                     |
# | VERSION: 0.3.2                                                      |
# | DATE:    2025-08-16                                                 |
# +=====================================================================+
# | ROLE: Sanity tests for kernel.smt_translator public API:            |
# |       - validate_ast accepts/ rejects proper ASTs                   |
# |       - compile_bool_ast accepts dict-based AST and populates       |
# |         symbol table with referenced variables.                     |
# | NOTE: These tests avoid runtime Z3 requirements; they do not        |
# |       inspect Z3 expressions deeply—only API/typing-level behavior. |
# +=====================================================================+

from __future__ import annotations

import pytest

from kernel.smt_translator import (
    ASTNode,
    compile_bool_ast,
    validate_ast,
)


# ----------------------------------------------------------------------
# Helpers to build small ASTs
# ----------------------------------------------------------------------
def v(name: str) -> ASTNode:
    return {"kind": "var", "name": name}  # type: ignore[typeddict-item]


def not_(arg: ASTNode) -> ASTNode:
    return {"kind": "unary", "op": "NOT", "arg": arg}  # type: ignore[typeddict-item]


def bin_(op: str, left: ASTNode, right: ASTNode) -> ASTNode:
    return {  # type: ignore[typeddict-item]
        "kind": "binary",
        "op": op,
        "left": left,
        "right": right,
    }


def nary_(op: str, *args: ASTNode) -> ASTNode:
    return {  # type: ignore[typeddict-item]
        "kind": "nary",
        "op": op,
        "args": list(args),
    }


# ----------------------------------------------------------------------
# Tests
# ----------------------------------------------------------------------
def test_validate_accepts_minimal_var_and_unary_and_binary():
    ast1: ASTNode = v("a")
    validate_ast(ast1)  # should not raise

    ast2: ASTNode = not_(v("b"))
    validate_ast(ast2)  # should not raise

    ast3: ASTNode = bin_("AND", v("a"), v("b"))
    validate_ast(ast3)  # should not raise


def test_validate_rejects_invalid_ops():
    bad_unary = {"kind": "unary", "op": "NEG", "arg": v("a")}  # type: ignore[typeddict-item]
    with pytest.raises(ValueError):
        validate_ast(bad_unary)  # invalid op

    bad_binary = {"kind": "binary", "op": "NAND", "left": v("a"), "right": v("b")}  # type: ignore[typeddict-item]
    with pytest.raises(ValueError):
        validate_ast(bad_binary)

    bad_nary = {"kind": "nary", "op": "XNOR", "args": [v("a"), v("b")]}  # type: ignore[typeddict-item]
    with pytest.raises(ValueError):
        validate_ast(bad_nary)


def test_compile_populates_symbol_table_for_vars():
    ast = bin_("OR", v("x"), not_(v("y")))
    _, symbols = compile_bool_ast(ast, validate=True)

    assert isinstance(symbols, dict)
    assert set(symbols.keys()) == {"x", "y"}


def test_compile_handles_nary_nodes():
    ast = nary_("AND", v("p"), v("q"), not_(v("r")))
    _, symbols = compile_bool_ast(ast, validate=True)
    assert set(symbols.keys()) == {"p", "q", "r"}
