#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/kernel/mismatch_protocol.py             |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


"""Protokół uruchamiany przy rozbieżności solverów — tworzy bilet."""

from __future__ import annotations

from typing import Any, Dict

from services.mismatch_service.service import mismatch_service


class MismatchError(RuntimeError):
    """Rzucane gdy wykryto niezgodność wyników solverów."""


def handle_mismatch(case_id: str, formula_str: str, results: Dict[str, Any]) -> None:
    ticket = mismatch_service.create_ticket(
        case_id=case_id,
        formula_str=formula_str,
        results=results,
        formula_ast=None,
    )
    raise MismatchError(
        f"Solver results are inconsistent. See ticket {ticket.ticket_id}."
    )
