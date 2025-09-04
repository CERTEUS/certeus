#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/demo_billing_pl/src/main.py                 |
# | ROLE: Project module.                                       |
# | PLIK: plugins/demo_billing_pl/src/main.py                 |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Wtyczka demo_billing_pl — proste API `handle(kind, payload)` dla billing tokens.
EN: demo_billing_pl plugin — simple `handle(kind, payload)` for billing tokens.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


class _Pack:
    def handle(self, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        if kind == "verify":
            rid = str(payload.get("request_id") or "")
            ok = len(rid) >= 8
            return {"ok": ok, "verified_request": rid}
        if kind == "quote":
            amt = int(payload.get("amount") or 0)
            return {"ok": True, "amount": amt, "price_usd": round(max(1, amt) * 0.01, 2)}
        return {"ok": False, "reason": f"unknown kind: {kind}"}


def register():
    return _Pack()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
