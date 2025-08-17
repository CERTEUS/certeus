#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/typings/z3/__init__.py                  |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/typings/z3/__init__.py          |
# | DATE:    2025-08-17                                          |
# +=====================================================================+
"""
PL: Pakiet inicjalizacyjny modułu.
EN: Package initializer.
"""

# -*- coding: utf-8 -*-
# +=====================================================================+
# |                              CERTEUS                                |
# |                          Typings for Z3 (stub)                      |
# +=====================================================================+
# | FILE: typings/z3/__init__.py                                        |
# | ROLE: Minimal type stubs for z3-solver, friendly to Pylance/Ruff    |
# +=====================================================================+

from typing import Any, Optional


class ExprRef: ...


class BoolRef(ExprRef): ...


class CheckSatResult: ...


class AstVector:
    def __len__(self) -> int: ...
    def __getitem__(self, i: int) -> ExprRef: ...


class Solver:
    def add(self, *args: Any) -> None: ...
    def check(self, *assumptions: Any) -> CheckSatResult: ...
    def model(self) -> Any: ...


def Bool(name: str, ctx: Optional[Any] = None) -> BoolRef: ...
def BoolVal(val: Any, ctx: Optional[Any] = None) -> BoolRef: ...
def And(*args: Any) -> ExprRef: ...
def Or(*args: Any) -> ExprRef: ...
def Not(a: Any) -> ExprRef: ...
def Implies(a: Any, b: Any) -> ExprRef: ...
def Xor(*args: Any) -> ExprRef: ...
def parse_smt2_string(s: str, decls: Optional[Any] = None) -> AstVector: ...
def get_version_string() -> str: ...


sat: CheckSatResult
unsat: CheckSatResult
unknown: CheckSatResult
