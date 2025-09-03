#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/proofgate_gateway.py   |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/proofgate_gateway.py   |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Alias/most do endpointu ProofGate w API Gateway, zgodny z kontraktem.
EN: Alias/bridge to ProofGate endpoint within the API Gateway, contract-aligned.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from typing import Any

from fastapi import APIRouter
from pydantic import BaseModel

# === MODELE / MODELS ===


class PublishRequest(BaseModel):
    pco: dict[str, Any] | None = None
    policy: dict[str, Any] | None = None
    budget_tokens: int | None = None


class PublishResponse(BaseModel):
    status: str
    pco: dict[str, Any] | None = None
    ledger_ref: str | None = None


# === LOGIKA / LOGIC ===

router = APIRouter(tags=["ProofGate"])


# === I/O / ENDPOINTS ===


@router.post("/v1/proofgate/publish", response_model=PublishResponse)
def publish_stub(req: PublishRequest) -> PublishResponse:  # pragma: no cover (kontrakt/openapi)
    """
    PL: Minimalny alias publikacji w bramce API – zapewnia zgodność OpenAPI.
    EN: Minimal publication alias in the API gateway – ensures OpenAPI compliance.
    """
    # Nie dublujemy pełnej logiki ProofGate tutaj; to jedynie alias kontraktowy
    # dla OpenAPI (runtime doc parity). Zwracamy neutralny status na wypadek
    # przeglądu w przeglądarce.
    return PublishResponse(status="PENDING", pco=req.pco, ledger_ref=None)


@router.post("/defx/reason", response_model=PublishResponse)
def defx_reason_stub(req: PublishRequest) -> PublishResponse:  # pragma: no cover
    """
    PL: Alias DEFx (legacy) zapewniający zgodność z kontraktem docs.
    EN: Legacy DEFx alias to satisfy docs contract parity.
    """
    return PublishResponse(status="PENDING", pco=req.pco, ledger_ref=None)


# === TESTY / TESTS ===
