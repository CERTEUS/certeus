#!/usr/bin/env python3
"""
PL: Pack SEC demo — prosta ocena ryzyka na podstawie listy luk.
EN: SEC demo pack — simple risk grading based on vulnerability list.
"""

from __future__ import annotations

from typing import Any


def register():  # noqa: D401 - demo register
    """Return handle-capable adapter for SEC demo."""

    def _grade(payload: dict[str, Any]) -> dict[str, Any]:
        vulns = list(payload.get("vulns") or [])
        n = len(vulns)
        if n >= 5:
            grade = "HIGH"
        elif n >= 2:
            grade = "MEDIUM"
        else:
            grade = "LOW"
        return {"risk_grade": grade, "count": n}

    def handle(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        k = (kind or "").strip().lower()
        if k in {"sec.risk.assess", "sec/risk/assess"}:
            return _grade(dict(payload or {}))
        return {"ok": False, "error": "unsupported kind"}

    return type("_Pack", (), {"handle": staticmethod(handle)})()
