#!/usr/bin/env python3
"""
PL: Pack CODE demo — prosta statyczna analiza (linie, TODO).
EN: CODE demo pack — simple static analysis (lines, TODO count).
"""

from __future__ import annotations

from typing import Any


def register():  # noqa: D401 - demo register
    """Return handle-capable adapter for CODE demo."""

    def _static(payload: dict[str, Any]) -> dict[str, Any]:
        src = str(payload.get("source") or "")
        lines = [ln for ln in src.splitlines()]
        todo = sum(1 for ln in lines if "TODO" in ln.upper())
        return {"lines": len(lines), "todo": todo}

    def handle(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        k = (kind or "").strip().lower()
        if k in {"code.static.check", "code/static/check"}:
            return _static(dict(payload or {}))
        return {"ok": False, "error": "unsupported kind"}

    return type("_Pack", (), {"handle": staticmethod(handle)})()
