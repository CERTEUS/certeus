#!/usr/bin/env python3
"""
PL: Pack demo LEX Casebook — zwraca listę ostatnich spraw Micro‑Court.
EN: LEX Casebook demo pack — returns latest Micro‑Court cases.
"""

from __future__ import annotations

from typing import Any


def register():  # noqa: D401 - simple register
    """Return handle-capable adapter for LEX Casebook."""

    def handle(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        k = (kind or "").strip().lower()
        if k in {"lex.casebook.latest", "lex/casebook/latest"}:
            try:
                # Import internal casebook from router
                from services.api_gateway.routers.lexenith import _CASEBOOK  # type: ignore

                limit = int(payload.get("limit", 3)) if isinstance(payload, dict) else 3
                items = list(_CASEBOOK[: max(1, limit)])
                return {"cases": items, "count": len(items)}
            except Exception as e:  # pragma: no cover - defensive
                return {"ok": False, "error": str(e)}
        return {"ok": False, "error": "unsupported kind"}

    return type("_Pack", (), {"handle": staticmethod(handle)})()
