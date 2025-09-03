#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/demo_beta/src/main.py                         |
# | ROLE: Demo plugin entry.                                     |
# | PLIK: plugins/demo_beta/src/main.py                          |
# | ROLA: Wejście wtyczki demo (Domain Pack).                    |
# +-------------------------------------------------------------+

"""
PL: Druga wtyczka demo – eksporter zwracający manifest.

EN: Second demo plugin – exporter returning its manifest.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


def register(api, name: str = "demo_beta") -> None:  # type: ignore[reportUnknownParameterType]
    """Register demo exporter under key 'demo.beta'."""

    def exporter(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        return {"demo": "beta", "kind": kind, "payload": dict(payload)}

    try:
        api.register_exporter("demo.beta", exporter)
    except Exception:
        if hasattr(api, "register"):
            api.register("demo.beta", exporter)
