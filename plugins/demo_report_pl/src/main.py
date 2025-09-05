#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/demo_report_pl/src/main.py                  |
# | ROLE: Project module.                                       |
# | PLIK: plugins/demo_report_pl/src/main.py                  |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Wtyczka demo_report_pl — generuje prosty raport JSON z payloadu.
EN: demo_report_pl plugin — generates a simple JSON report from payload.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


class _Pack:
    def handle(self, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        if kind == "summarize":
            title = str(payload.get("title") or "Report")
            items = list(payload.get("items") or [])
            return {
                "ok": True,
                "title": title,
                "count": len(items),
                "preview": items[:3],
            }
        return {"ok": False, "reason": f"unknown kind: {kind}"}


def register():
    return _Pack()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
