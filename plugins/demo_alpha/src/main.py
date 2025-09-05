#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/demo_alpha/src/main.py                        |
# | ROLE: Demo plugin entry.                                     |
# | PLIK: plugins/demo_alpha/src/main.py                         |
# | ROLA: Wejście wtyczki demo (Domain Pack).                    |
# +-------------------------------------------------------------+

"""
PL: Wtyczka demo – rejestruje prosty adapter w API pluginów.

EN: Demo plugin – registers a simple adapter into the plugin API.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


def register(api, name: str = "demo_alpha") -> None:  # type: ignore[reportUnknownParameterType]
    """Register demo adapter under key 'demo.alpha'."""

    def adapter(kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        return {"kind": kind, "echo": dict(payload)}

    try:
        api.register_adapter("demo.alpha", adapter)
    except Exception:
        # Fallback: allow both styles depending on API
        if hasattr(api, "register"):
            api.register("demo.alpha", adapter)
