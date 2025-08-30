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
import services.api_gateway.routers.cfe as cfe
import services.api_gateway.routers.chatops as chatops
import services.api_gateway.routers.devices as devices
import services.api_gateway.routers.dr as dr
import services.api_gateway.routers.ethics as ethics
import services.api_gateway.routers.export as export
import services.api_gateway.routers.fin as fin
import services.api_gateway.routers.ledger as ledger
import services.api_gateway.routers.lexqft as lexqft
import services.api_gateway.routers.mailops as mailops
import services.api_gateway.routers.mismatch as mismatch
import services.api_gateway.routers.packs as packs
import services.api_gateway.routers.pco_public as pco_public
import services.api_gateway.routers.preview as preview
import services.api_gateway.routers.qtm as qtm
import services.api_gateway.routers.system as system  # /v1/ingest, /v1/analyze, /v1/sipp
import services.api_gateway.routers.upn as upn
import services.api_gateway.routers.verify as verify
from services.api_gateway.routers.well_known_jwks import router as jwks_router
from services.api_gateway.security import attach_proof_only_middleware
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

# Attach Proof-Only I/O middleware early (safe no-op unless STRICT_PROOF_ONLY=1)
attach_proof_only_middleware(app)


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
app.include_router(cfe.router)
app.include_router(qtm.router)
app.include_router(devices.router)
app.include_router(dr.router)
app.include_router(upn.router)
app.include_router(lexqft.router)
app.include_router(chatops.router)
app.include_router(mailops.router)
app.include_router(ethics.router)
app.include_router(fin.router)
app.include_router(packs.router)
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
