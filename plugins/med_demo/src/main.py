#!/usr/bin/env python3
"""
PL: Pack MED demo — prosta redakcja PHI w tekście.
EN: MED demo pack — simple PHI redaction in text.
"""

from __future__ import annotations

import re
from typing import Any


def register():  # noqa: D401 - demo register
    """Return handle-capable adapter for MED demo."""

    _rx_phi = re.compile(r"\b(PESEL|SSN|DOB|MRN)\s*[:=]\s*\S+", re.IGNORECASE)

    def _redact(payload: dict[str, Any]) -> dict[str, Any]:
        txt = str(payload.get("text") or "")
        red = _rx_phi.sub(lambda m: m.group(0).split(" ")[0] + " [REDACTED]", txt)
        return {"redacted": red, "pco": {"med.phi.redaction": {"ok": red != txt}}}

    def handle(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        k = (kind or "").strip().lower()
        if k in {"med.phi.redact", "med/phi/redact"}:
            return _redact(dict(payload or {}))
        return {"ok": False, "error": "unsupported kind"}

    return type("_Pack", (), {"handle": staticmethod(handle)})()
