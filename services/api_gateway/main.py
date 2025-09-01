#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/main.py                        |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/main.py                        |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Główna aplikacja FastAPI dla CERTEUS: statyki, routery, CORS (DEV), health.

EN: Main FastAPI app for CERTEUS: statics, routers, CORS (DEV), health.

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from contextlib import asynccontextmanager

import os

from pathlib import Path

from fastapi import FastAPI, UploadFile

from fastapi.middleware.cors import CORSMiddleware

from fastapi.responses import RedirectResponse

from fastapi.staticfiles import StaticFiles

from core.version import __version__

from monitoring.metrics_slo import certeus_http_request_duration_ms

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

import services.api_gateway.routers.metrics as metrics

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

# === KONFIGURACJA / CONFIGURATION ===
APP_TITLE = "CERTEUS API Gateway"

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===









ROOT = Path(__file__).resolve().parents[2]

STATIC_DIR = ROOT / "static"

STATIC_PREVIEWS = STATIC_DIR / "previews"

CLIENTS_WEB = ROOT / "clients" / "web"  # expects /app/proof_visualizer/index.html


APP_VERSION = __version__

ALLOW_ORIGINS_ENV = os.getenv("ALLOW_ORIGINS", "*")

DEV_ORIGINS: list[str] = (
    [o.strip() for o in ALLOW_ORIGINS_ENV.split(",") if o.strip()]
    if ALLOW_ORIGINS_ENV and ALLOW_ORIGINS_ENV != "*"
    else ["*"]
)


#!/usr/bin/env python3


# --- blok --- Importy ----------------------------------------------------------


# stdlib

# third-party


# local (rozbite na pojedyncze linie — łatwiej sortować i Ruff nie marudzi)

# pco_bundle is optional in CI: import lazily and guard include
try:  # pragma: no cover - best-effort import for optional router
    import services.api_gateway.routers.pco_bundle as pco_bundle  # type: ignore
except Exception as _e:  # ModuleNotFoundError or dependency errors
    pco_bundle = None  # type: ignore[assignment]

# --- blok --- Ścieżki i katalogi ----------------------------------------------


STATIC_PREVIEWS.mkdir(parents=True, exist_ok=True)

CLIENTS_WEB.mkdir(parents=True, exist_ok=True)


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


# CORS: configurable via ALLOW_ORIGINS (comma-separated); default "*"


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

if pco_bundle is not None:  # only include if import succeeded
    app.include_router(pco_bundle.router)

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

app.include_router(metrics.router)


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


# --- blok --- Metrics middleware (request duration) -----------------------------


@app.middleware("http")
async def _metrics_timing(request, call_next):  # type: ignore[override]
    import time as _t

    start = _t.perf_counter()

    response = await call_next(request)

    try:
        route = request.scope.get("route")

        path_tmpl = getattr(route, "path", request.url.path)

        status = getattr(response, "status_code", 0)

        certeus_http_request_duration_ms.labels(path=path_tmpl, method=request.method, status=str(status)).observe(
            (_t.perf_counter() - start) * 1000.0
        )

    except Exception:
        pass

    return response



# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

