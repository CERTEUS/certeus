#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/packs_sec/src/main.py                        |
# | ROLE: Project module.                                       |
# | PLIK: plugins/packs_sec/src/main.py                        |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Wtyczka packs_sec — demo „SEC” (MVP). Rejestruje prosty audyt polityk
    i eksporter „sec.audit.json”.

EN: packs_sec plugin — demo "SEC" (MVP). Registers a simple policy audit
    and exporter "sec.audit.json".
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


class _Pack:
    def handle(self, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        if kind == "policy.audit":
            pol = dict(payload.get("policy") or {})
            name = str(pol.get("name") or "demo-policy")
            required = set(pol.get("required", []))
            provided = set(pol.get("provided", []))
            missing = sorted(list(required - provided))
            result = {"name": name, "missing": missing, "ok": not missing}
            pco = {
                "sec.policy.audit": result,
                # Governance linkage (informational)
                "consent_ref": "consent://policies",
            }
            return {"result": result, "pco": pco}
        return {"ok": False, "reason": f"unknown kind: {kind}"}


def register(api: Any | None = None) -> _Pack | None:
    if api is not None and hasattr(api, "register_exporter"):

        def _export_audit(sample: dict[str, Any], fmt: str = "json") -> dict[str, Any]:
            return {"fmt": fmt, "sec_audit": sample}

        api.register_exporter("sec.audit.json", _export_audit)
        return None
    return _Pack()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
