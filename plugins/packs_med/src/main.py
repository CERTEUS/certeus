#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: plugins/packs_med/src/main.py                        |
# | ROLE: Project module.                                       |
# | PLIK: plugins/packs_med/src/main.py                        |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Wtyczka packs_med — demo „MED” (MVP). Rejestruje exporter „med.report.json”
    i udostępnia handle(kind,payload) zwracające prosty PCO‑like wynik.

EN: packs_med plugin — demo "MED" (MVP). Registers exporter "med.report.json"
    and exposes handle(kind,payload) returning a simple PCO‑like result.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any


class _Pack:
    def handle(self, kind: str, payload: dict[str, Any]) -> dict[str, Any]:
        if kind == "case.summary":
            subj = str(payload.get("subject") or "MED-CASE")
            risk = float(payload.get("risk_index") or 0.1)
            body = {"subject": subj, "risk_index": round(risk, 3)}
            # Minimal PCO-like structure for packs
            pco = {"med.case.summary": body}
            return {"summary": body, "pco": pco}
        return {"ok": False, "reason": f"unknown kind: {kind}"}


def register(api: Any | None = None) -> _Pack | None:
    """
    PL: Rejestracja packa. Jeśli podano `api`, rejestruje eksporter best‑effort.
    EN: Pack registration. If `api` provided, registers a best‑effort exporter.
    """
    if api is not None and hasattr(api, "register_exporter"):
        # Minimalny eksporter JSON – echo payload, aby /v1/packs/try mogło coś zwrócić
        def _export_med(sample: dict[str, Any], fmt: str = "json") -> dict[str, Any]:
            return {"fmt": fmt, "med": sample}

        api.register_exporter("med.report.json", _export_med)
        return None
    # Bez API zwracamy obiekt z handle() na potrzeby /v1/packs/handle
    return _Pack()


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
