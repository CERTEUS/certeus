#!/usr/bin/env python3
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE / MODUŁ: services/api_gateway/main.py                        |
# | DATE / DATA: 2025-08-19                                             |
# +=====================================================================+
# | ROLE / ROLA:                                                        |
# |  EN: API Gateway bootstrap. Mounts static, registers routers,       |
# |      enables DEV CORS, exposes health and root redirect.            |
# |  PL: Bootstrap bramy API. Montuje statyczne zasoby, rejestruje      |
# |      routery, włącza CORS (DEV), wystawia health i redirect root.   |
# +=====================================================================+

"""
PL: Główna aplikacja FastAPI dla CERTEUS: statyki, routery, CORS (DEV), health.
EN: Main FastAPI app for CERTEUS: statics, routers, CORS (DEV), health.
"""

# --- blok --- Importy ----------------------------------------------------------
from __future__ import annotations

# stdlib
from contextlib import asynccontextmanager
from pathlib import Path

# third-party
from fastapi import FastAPI, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import RedirectResponse
from fastapi.staticfiles import StaticFiles

# local (rozbite na pojedyncze linie — łatwiej sortować i Ruff nie marudzi)
from services.api_gateway.routers import (
    export,
    ledger,
    mismatch,
    pco_public,
    preview,
    system,  # /v1/ingest, /v1/analyze, /v1/sipp
    verify,
)
from services.api_gateway.routers.well_known_jwks import router as jwks_router
from services.ingest_service.adapters.contracts import Blob
from services.ingest_service.adapters.registry import get_llm, get_preview

# --- blok --- Ścieżki i katalogi ----------------------------------------------

ROOT = Path(__file__).resolve().parents[2]
STATIC_DIR = ROOT / "static"
STATIC_PREVIEWS = STATIC_DIR / "previews"
CLIENTS_WEB = ROOT / "clients" / "web"  # expects /app/proof_visualizer/index.html

STATIC_PREVIEWS.mkdir(parents=True, exist_ok=True)
CLIENTS_WEB.mkdir(parents=True, exist_ok=True)

APP_TITLE = "CERTEUS API Gateway"
APP_VERSION = "1.1.5"

# --- blok --- Lifespan (inicjalizacja adapterów) -------------------------------


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    PL: Leniwe utworzenie singletonów adapterów przy starcie.
    EN: Lazily create adapter singletons on startup.
    """
    _ = (get_preview(), get_llm())
    yield


# --- blok --- Aplikacja i middleware -------------------------------------------

app = FastAPI(
    title=APP_TITLE,
    version=APP_VERSION,
    docs_url="/docs",
    redoc_url="/redoc",
    openapi_url="/openapi.json",
    lifespan=lifespan,
)


# statyki
app.mount("/static", StaticFiles(directory=str(STATIC_DIR)), name="static")
app.mount("/app", StaticFiles(directory=str(CLIENTS_WEB)), name="app")

# CORS (DEV) – szeroko, bez credentials
DEV_ORIGINS: list[str] = ["*"]
app.add_middleware(
    CORSMiddleware,
    allow_origins=DEV_ORIGINS,
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)

# --- blok --- Rejestr routerów -------------------------------------------------

app.include_router(system.router)
app.include_router(preview.router)
app.include_router(pco_public.router)
app.include_router(export.router)
app.include_router(ledger.router)
app.include_router(mismatch.router)
app.include_router(verify.router)
app.include_router(jwks_router)

# --- blok --- Health i root redirect -------------------------------------------


@app.get("/health")
def health() -> dict[str, object]:
    """PL: Liveness; EN: Liveness."""
    return {"status": "ok", "version": APP_VERSION}


@app.get("/")
def root_redirect() -> RedirectResponse:
    """
    PL: W DEV kierujemy na UI wizualizatora.
    EN: In DEV, redirect to the proof visualizer UI.
    """
    return RedirectResponse(url="/app/proof_visualizer/index.html", status_code=307)


# --- blok --- Pomocnicze -------------------------------------------------------


def _make_blob(upload: UploadFile, data: bytes) -> Blob:
    """
    PL: Buduje Blob z UploadFile.
    EN: Build Blob from UploadFile.
    """
    return Blob(
        filename=upload.filename or "file",
        content_type=upload.content_type or "application/octet-stream",
        data=data,
    )
