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
    Udostępnia ten sam `router` co `billing.router_tokens`.

EN: Router alias for legacy `fin_tokens_api` import path.
    Exposes the same `router` as `billing.router_tokens`.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from services.api_gateway.routers import billing

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# Public alias expected by `services.api_gateway.main`
router = billing.router_tokens

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
