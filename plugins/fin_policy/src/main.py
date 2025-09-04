#!/usr/bin/env python3
"""
PL: Pack demo FIN Policy — sprawdza progi ryzyka/sentymentu.
EN: FIN Policy demo pack — checks risk/sentiment thresholds.
"""

from __future__ import annotations

from typing import Any


def register():  # noqa: D401 - simple register
    """Return handle-capable adapter for FIN Policy."""

    def _check(payload: dict[str, Any]) -> dict[str, Any]:
        sig = dict(payload.get("signals") or {})
        risk = float(sig.get("risk", 0.0))
        sent = float(sig.get("sentiment", sig.get("sent", 0.0)))
        thr = dict(payload.get("thresholds") or {})
        risk_max = float(thr.get("risk_max", 0.9))
        sent_min = float(thr.get("sentiment_min", -1.0))
        ok = True
        viol: list[str] = []
        if risk > risk_max:
            ok = False
            viol.append("risk_above_max")
        if sent < sent_min:
            ok = False
            viol.append("sentiment_below_min")
        return {"policy_ok": ok, "violations": viol, "thresholds": {"risk_max": risk_max, "sentiment_min": sent_min}}

    def handle(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        k = (kind or "").strip().lower()
        if k in {"fin.policy.check", "fin/policy/check"}:
            return _check(dict(payload or {}))
        return {"ok": False, "error": "unsupported kind"}

    return type("_Pack", (), {"handle": staticmethod(handle)})()
