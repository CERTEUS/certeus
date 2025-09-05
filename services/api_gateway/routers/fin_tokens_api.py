#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/fin_tokens_api.py       |
# | ROLE: Compatibility router alias for Billing tokens         |
# | PLIK: services/api_gateway/routers/fin_tokens_api.py       |
# | ROLA: Alias kompatybilności dla routera Billing tokens      |
# +-------------------------------------------------------------+
"""
PL: Alias routera dla historycznej ścieżki `fin_tokens_api`.
    Wystawia te same endpointy co `billing.router_tokens`, ale jako osobny
    router z wyłączonym uwzględnieniem w schemacie (include_in_schema=False),
    aby uniknąć duplikatów operationId w OpenAPI.

EN: Router alias for legacy `fin_tokens_api` import path.
    Exposes the same endpoints as `billing.router_tokens`, but via a separate
    router with include_in_schema=False to avoid duplicate operationIds in
    OpenAPI.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Request

from services.api_gateway.routers import billing

# Re-export models to keep type signatures stable for wrappers
TokenRequestIn = billing.TokenRequestIn
TokenRequestOut = billing.TokenRequestOut
TokenAllocateIn = billing.TokenAllocateIn
TokenStatusOut = billing.TokenStatusOut

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# Public alias expected by `services.api_gateway.main`.
# We provide a thin wrapper router that calls through to billing.* handlers
# and is excluded from OpenAPI (no duplicates in docs).
router = APIRouter(prefix="/v1/fin/tokens", tags=["billing"])


@router.post(
    "/request",
    response_model=TokenRequestOut,
    operation_id="fin_legacy_request_tokens",
    include_in_schema=False,
)
async def legacy_request_tokens(req: TokenRequestIn, request: Request) -> TokenRequestOut:
    return await billing.request_tokens(req, request)


@router.post(
    "/allocate",
    response_model=TokenStatusOut,
    operation_id="fin_legacy_allocate_tokens",
    include_in_schema=False,
)
async def legacy_allocate_tokens(req: TokenAllocateIn, request: Request) -> TokenStatusOut:
    return await billing.allocate_tokens(req, request)


@router.get(
    "/{request_id}",
    response_model=TokenStatusOut,
    operation_id="fin_legacy_get_token_request_status",
    include_in_schema=False,
)
async def legacy_get_token_request_status(request_id: str, request: Request) -> TokenStatusOut:
    return await billing.get_request_status(request_id, request)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
