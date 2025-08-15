# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/main.py                          |
# | ROLE: FastAPI application wiring public routers & /health.  |
# | PLIK: services/api_gateway/main.py                          |
# | ROLA: Aplikacja FastAPI spinająca routery publiczne i /health|
# +-------------------------------------------------------------+
"""
PL: Główna aplikacja API. Dołącza routery (w tym /v1/verify) oraz /health.
EN: Main API app. Attaches routers (including /v1/verify) and /health.
"""

# === IMPORTY / IMPORTS ======================================== #
from __future__ import annotations

from fastapi import FastAPI

# [ROUTER IMPORTS – BEZPOŚREDNIO Z MODUŁÓW]
# Wymagany przez Dzień 5: /v1/verify
from services.api_gateway.routers.verify import router as verify_router

# Opcjonalne – jeśli masz te moduły w repo, podepniemy ich routery;
# jeśli nie, continue gracefully.
try:
    from services.api_gateway.routers.system import router as system_router  # type: ignore
except Exception:  # pragma: no cover
    system_router = None  # type: ignore

try:
    from services.api_gateway.routers.export import router as export_router  # type: ignore
except Exception:  # pragma: no cover
    export_router = None  # type: ignore

try:
    from services.api_gateway.routers.ledger import router as ledger_router  # type: ignore
except Exception:  # pragma: no cover
    ledger_router = None  # type: ignore


# === APLIKACJA / APP ========================================== #
app = FastAPI(title="CERTEUS API", version="1.0")


# === REJESTRACJA ROUTERÓW / ROUTER REGISTRATION =============== #
# Kluczowe: verify – dodaje ścieżkę /v1/verify do OpenAPI
app.include_router(verify_router)

# Opcjonalne (jeśli moduły istnieją u Ciebie w repo):
if system_router is not None:
    app.include_router(system_router)
if export_router is not None:
    app.include_router(export_router)
if ledger_router is not None:
    app.include_router(ledger_router)


# === HEALTHCHECK ============================================== #
@app.get("/health")
def health() -> dict[str, bool]:
    """
    PL: Prosty endpoint sprawdzający żywotność API.
    EN: Simple endpoint to check API liveness.
    """
    return {"ok": True}
