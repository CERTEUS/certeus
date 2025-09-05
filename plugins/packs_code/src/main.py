#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/packs_code/src/main.py                       |
# | ROLE: Project module.                                       |
# | PLIK: plugins/packs_code/src/main.py                       |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Wtyczka packs_code — demo „CODE” (MVP). Rejestruje eksporter „code.normalize.json”
    i handle(kind,payload) dla prostych operacji na tekście.

EN: packs_code plugin — demo "CODE" (MVP). Registers exporter "code.normalize.json"
    and handle(kind,payload) for simple text operations.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


class _Pack:
    def handle(self, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        if kind == "text.normalize":
            text = str(payload.get("text") or "")
            norm = " ".join(text.split())
            result = {"len": len(norm), "text": norm}
            pco = {"code.text.normalize": {"len": len(norm)}}
            return {"result": result, "pco": pco}
        return {"ok": False, "reason": f"unknown kind: {kind}"}


def register(api: Any | None = None) -> _Pack | None:
    if api is not None and hasattr(api, "register_exporter"):

        def _export_norm(sample: dict[str, Any], fmt: str = "json") -> dict[str, Any]:
            return {"fmt": fmt, "code": sample}

        api.register_exporter("code.normalize.json", _export_norm)
        return None
    return _Pack()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
