#!/usr/bin/env python3
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE / MODUŁ: services/api_gateway/main.py                        |
# | DATE / DATA: 2025-08-17                                             |
# +=====================================================================+
# | ROLE / ROLA:                                                        |
# |  EN: API Gateway bootstrap. Mounts static, registers routers,       |
# |      enables DEV CORS, exposes health and root redirect.            |
# |  PL: Bootstrap bramy API. Montuje statyczne zasoby, rejestruje      |
# |      routery, włącza CORS (DEV), wystawia health i redirect root.   |
# +=====================================================================+

"""
PL: Główna aplikacja FastAPI dla CERTEUS. Serwuje statyczne zasoby (/app, /static),
    rejestruje routery (verify, mismatch, export, ledger, system, preview),
    w DEV włącza luźny CORS i przekierowuje "/" na UI wizualizatora.
EN: Main FastAPI app for CERTEUS. Serves static assets (/app, /static),
    registers routers (verify, mismatch, export, ledger, system, preview),
    enables permissive CORS in DEV, and redirects "/" to the visualizer UI.
"""

from __future__ import annotations

from pathlib import Path

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import RedirectResponse
from fastapi.staticfiles import StaticFiles

# Routers available in repo
from services.api_gateway.routers import (
    export,
    ledger,
    mismatch,
    preview,
    system,  # /v1/ingest, /v1/analyze, /v1/sipp
    verify,
)

# === PATHS / ŚCIEŻKI ===
ROOT = Path(__file__).resolve().parents[2]
STATIC_DIR = ROOT / "static"
STATIC_PREVIEWS = STATIC_DIR / "previews"
CLIENTS_WEB = ROOT / "clients" / "web"  # expects /app/proof_visualizer/index.html

# Ensure present / Utwórz jeśli brak (DEV)
STATIC_PREVIEWS.mkdir(parents=True, exist_ok=True)
CLIENTS_WEB.mkdir(parents=True, exist_ok=True)

APP_TITLE = "CERTEUS API Gateway"
APP_VERSION = "1.1.4"

app = FastAPI(
    title=APP_TITLE,
    version=APP_VERSION,
    docs_url="/docs",
    redoc_url="/redoc",
    openapi_url="/openapi.json",
)

# === STATIC MOUNTS ===
app.mount("/static", StaticFiles(directory=str(STATIC_DIR)), name="static")
app.mount("/app", StaticFiles(directory=str(CLIENTS_WEB)), name="app")

# === CORS (DEV) — permissive origins, no credentials ===
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)

# === ROUTERS ===
app.include_router(verify.router)
app.include_router(mismatch.router)
app.include_router(export.router)
app.include_router(ledger.router)
app.include_router(system.router)
app.include_router(preview.router)


# === HEALTH ===
@app.get("/health")
def health() -> dict[str, object]:
    """PL: Liveness; EN: Liveness."""
    return {"status": "ok", "version": APP_VERSION}


# === ROOT REDIRECT → UI ===
@app.get("/")
def root_redirect() -> RedirectResponse:
    """
    PL: W DEV kierujemy na UI wizualizatora.
    EN: In DEV, redirect to the proof visualizer UI.
    """
    return RedirectResponse(url="/app/proof_visualizer/index.html", status_code=307)
