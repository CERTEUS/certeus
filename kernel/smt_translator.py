#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: kernel/smt_translator.py                            |

# | ROLE: Project module.                                       |

# | PLIK: kernel/smt_translator.py                            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Translator SMT i powiązana logika.

EN: SMT translator and related logic.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections.abc import Mapping
from typing import Any, Literal, TypedDict, cast

import z3  # type: ignore[reportMissingTypeStubs]

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
class VarNode(TypedDict):
    kind: Literal["var"]

    name: str


class UnaryNode(TypedDict):
    kind: Literal["unary"]

    op: Literal["NOT"]

    arg: Any


class BinaryNode(TypedDict):
    kind: Literal["binary"]

    op: Literal["AND", "OR", "IMPLIES", "XOR"]

    left: Any

    right: Any


class NaryNode(TypedDict):
    kind: Literal["nary"]

    op: Literal["AND", "OR", "XOR"]

    args: list[Any]


# === LOGIKA / LOGIC ===


_Z3 = cast(Any, z3)  # ✅ correct use of typing.cast


#!/usr/bin/env python3


# ──────────────────────────────────────────────────────────────────────

# AST (TypedDict)

# ──────────────────────────────────────────────────────────────────────


ASTNode = VarNode | UnaryNode | BinaryNode | NaryNode


# ──────────────────────────────────────────────────────────────────────

# Helpers

# ──────────────────────────────────────────────────────────────────────


def _normalize(node: ASTNode | Mapping[str, Any]) -> ASTNode:
    """Allow Mapping (dict-like) in public API; normalize to plain dict."""

    return cast(ASTNode, dict(node)) if isinstance(node, Mapping) else node


def validate_ast(node: ASTNode | Mapping[str, Any]) -> None:
    n0 = _normalize(node)

    k = n0.get("kind")  # type: ignore[assignment]

    if k == "var":
        n = cast(VarNode, n0)

        if not n["name"] or not isinstance(n["name"], str):
            raise ValueError("Var.name must be non-empty string")

    elif k == "unary":
        u = cast(UnaryNode, n0)

        if u["op"] != "NOT":
            raise ValueError("unary.op must be 'NOT'")

        validate_ast(cast(ASTNode, u["arg"]))

    elif k == "binary":
        b = cast(BinaryNode, n0)

        if b["op"] not in {"AND", "OR", "IMPLIES", "XOR"}:
            raise ValueError("binary.op invalid")

        validate_ast(cast(ASTNode, b["left"]))

        validate_ast(cast(ASTNode, b["right"]))

    elif k == "nary":
        n = cast(NaryNode, n0)

        if n["op"] not in {"AND", "OR", "XOR"}:
            raise ValueError("nary.op invalid")

        for a in n["args"]:
            validate_ast(cast(ASTNode, a))

    else:
        raise ValueError("Unknown AST kind")


def _ensure_sym(symbols: dict[str, z3.ExprRef], name: str) -> z3.ExprRef:
    if name not in symbols:
        # In some local stubs BoolRef may not subclass ExprRef → cast to keep Pylance happy

        symbols[name] = cast("z3.ExprRef", _Z3.Bool(name))

    return symbols[name]


def _compile(node: ASTNode, symbols: dict[str, z3.ExprRef]) -> z3.ExprRef:
    k = node["kind"]

    if k == "var":
        name = cast(VarNode, node)["name"]

        return _ensure_sym(symbols, name)

    if k == "unary":
        arg = _compile(cast(UnaryNode, node)["arg"], symbols)

        return cast("z3.ExprRef", _Z3.Not(arg))

    if k == "binary":
        b = cast(BinaryNode, node)

        lhs = _compile(cast(ASTNode, b["left"]), symbols)  # ✅ no ambiguous 'l'

        rhs = _compile(cast(ASTNode, b["right"]), symbols)

        op = b["op"]

        if op == "AND":
            return cast("z3.ExprRef", _Z3.And(lhs, rhs))

        if op == "OR":
            return cast("z3.ExprRef", _Z3.Or(lhs, rhs))

        if op == "IMPLIES":
            return cast("z3.ExprRef", _Z3.Implies(lhs, rhs))

        if op == "XOR":
            return cast("z3.ExprRef", _Z3.Xor(lhs, rhs))

        raise AssertionError("unreachable")

    # nary

    n = cast(NaryNode, node)

    args = [_compile(cast(ASTNode, a), symbols) for a in n["args"]]

    if n["op"] == "AND":
        return cast("z3.ExprRef", _Z3.And(*args))

    if n["op"] == "OR":
        return cast("z3.ExprRef", _Z3.Or(*args))

    if n["op"] == "XOR":
        return cast("z3.ExprRef", _Z3.Xor(*args))

    raise AssertionError("unreachable")


# ──────────────────────────────────────────────────────────────────────

# Public API

# ──────────────────────────────────────────────────────────────────────


def compile_bool_ast(
    node: ASTNode | Mapping[str, Any],
    *,
    declare_on_use: bool = True,  # kept for API symmetry
    validate: bool = True,
) -> tuple[z3.ExprRef, dict[str, z3.ExprRef]]:
    if validate:
        validate_ast(node)

    ast = _normalize(node)

    symbols: dict[str, z3.ExprRef] = {}

    expr = _compile(ast, symbols)

    return expr, symbols


__all__ = [
    "VarNode",
    "UnaryNode",
    "BinaryNode",
    "NaryNode",
    "ASTNode",
    "validate_ast",
    "compile_bool_ast",
]


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
