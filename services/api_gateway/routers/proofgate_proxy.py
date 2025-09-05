#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/proofgate_proxy.py       |
# | ROLE: API stub.                                              |
# | PLIK: services/api_gateway/routers/proofgate_proxy.py       |
# | ROLA: Stub endpoint zgodny z kontraktem /v1/proofgate/publish|
# +-------------------------------------------------------------+

"""
PL: Lekki stub /v1/proofgate/publish na potrzeby zgodności OpenAPI po stronie
    API Gateway (faktyczna implementacja żyje w services.proofgate.app).

EN: Lightweight stub of /v1/proofgate/publish for OpenAPI compatibility on the
    API Gateway side (actual implementation lives in services.proofgate.app).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any

from fastapi import APIRouter

router = APIRouter()

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


@router.post("/v1/proofgate/publish")
def publish_stub(body: dict[str, Any] | None = None) -> dict[str, Any]:
    """PL/EN: Stub zwracający decyzję PENDING (zgodny z kontraktem)."""

    return {"status": "PENDING", "pco": (body or {}).get("pco"), "ledger_ref": None}


# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
