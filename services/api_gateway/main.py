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
from fastapi.openapi.utils import get_openapi
from fastapi.responses import RedirectResponse
from fastapi.staticfiles import StaticFiles

from core.version import __version__
from monitoring.otel_setup import setup_fastapi_otel
from services.api_gateway.rate_limit import attach_rate_limit_middleware
import services.api_gateway.routers.billing as billing
import services.api_gateway.routers.billing_api as billing_api
import services.api_gateway.routers.billing_quota as billing_quota
import services.api_gateway.routers.boundary as boundary
import services.api_gateway.routers.cfe as cfe
import services.api_gateway.routers.chatops as chatops
import services.api_gateway.routers.devices as devices
import services.api_gateway.routers.dr as dr
import services.api_gateway.routers.ethics as ethics
import services.api_gateway.routers.export as export
import services.api_gateway.routers.fin as fin
import services.api_gateway.routers.ledger as ledger
import services.api_gateway.routers.lexenith as lexenith
import services.api_gateway.routers.lexqft as lexqft
import services.api_gateway.routers.mailops as mailops
import services.api_gateway.routers.marketplace as marketplace
import services.api_gateway.routers.metrics as metrics
import services.api_gateway.routers.mismatch as mismatch
import services.api_gateway.routers.openapi_docs as openapi_docs
import services.api_gateway.routers.p2p as p2p
import services.api_gateway.routers.packs as packs
import services.api_gateway.routers.pfs as pfs
import services.api_gateway.routers.pfs_dht as pfs_dht
import services.api_gateway.routers.preview as preview
import services.api_gateway.routers.proofgate_gateway as proofgate_gateway
import services.api_gateway.routers.qoc as qoc
import services.api_gateway.routers.qtm as qtm
import services.api_gateway.routers.system as system  # /v1/ingest, /v1/analyze, /v1/sipp
import services.api_gateway.routers.tee as tee
import services.api_gateway.routers.upn as upn
import services.api_gateway.routers.verify as verify
from services.api_gateway.routers.well_known_jwks import router as jwks_router
from services.api_gateway.security import attach_proof_only_middleware
from services.api_gateway.shedder import attach_shedder_middleware
from services.ingest_service.adapters.contracts import Blob
from services.ingest_service.adapters.registry import get_llm, get_preview

# Optional routers that may be absent depending on build profile
try:  # optional legacy alias; may be absent in some trees
    import services.api_gateway.routers.fin_tokens_api as fin_tokens_api  # type: ignore
except Exception:
    fin_tokens_api = None  # type: ignore[assignment]
try:  # optional: avoid hard fail if core/pco deps are unavailable
    import services.api_gateway.routers.pco_public as pco_public  # type: ignore
except Exception:
    pco_public = None  # type: ignore[assignment]

# === KONFIGURACJA / CONFIGURATION ===

APP_TITLE = "CERTEUS API Gateway"

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

ROOT = Path(__file__).resolve().parents[2]

STATIC_DIR = ROOT / "static"

STATIC_PREVIEWS = STATIC_DIR / "previews"

CLIENTS_WEB = ROOT / "clients" / "web"  # expects /app/proof_visualizer/index.html

# API versioning: semver for contract, full release for build metadata
APP_RELEASE = __version__
APP_VERSION = (__version__.split("-", 1)[0] or __version__).strip()

ALLOW_ORIGINS_ENV = os.getenv("ALLOW_ORIGINS", "*")

DEV_ORIGINS: list[str] = (
    [o.strip() for o in ALLOW_ORIGINS_ENV.split(",") if o.strip()]
    if ALLOW_ORIGINS_ENV and ALLOW_ORIGINS_ENV != "*"
    else ["*"]
)

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

# Optional: OpenTelemetry auto-instrumentation (OTEL_ENABLED=1)
setup_fastapi_otel(app)

# Optional: Rate-limit middleware (enable via RATE_LIMIT_QPS)
attach_rate_limit_middleware(app)
attach_shedder_middleware(app)

# statyki

app.mount("/static", StaticFiles(directory=str(STATIC_DIR)), name="static")

app.mount("/app", StaticFiles(directory=str(CLIENTS_WEB)), name="app")

# Serve repository docs for simple in-app linking (read-only)
try:  # pragma: no cover
    app.mount("/docs", StaticFiles(directory=str(ROOT / "docs")), name="docs")
except Exception:
    pass

# Backward-compat: serve marketplace.html from clients/web/public if not at root
from fastapi.responses import FileResponse  # noqa: E402


@app.get("/app/marketplace.html")
def _serve_marketplace():
    cand = CLIENTS_WEB / "marketplace.html"
    if not cand.exists():
        cand = CLIENTS_WEB / "public" / "marketplace.html"
    return FileResponse(str(cand))


# CORS: configurable via ALLOW_ORIGINS (comma-separated); default "*"

app.add_middleware(
    CORSMiddleware,
    allow_origins=DEV_ORIGINS,
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)


# Simple i18n negotiation: query param `lang` overrides `Accept-Language`.
# Sets `request.state.lang` and adds `Content-Language` response header.
@app.middleware("http")
async def _i18n_language_negotiator(request, call_next):  # type: ignore[no-redef]
    def _pick_lang(raw: str | None) -> str:
        if not raw:
            return "pl"
        s = raw.lower()
        if "en" in s:
            return "en"
        if "pl" in s:
            return "pl"
        return "pl"

    qp_lang = request.query_params.get("lang")
    hdr_lang = request.headers.get("accept-language")
    lang = _pick_lang(qp_lang or hdr_lang)
    try:
        request.state.lang = lang  # type: ignore[attr-defined]
    except Exception:
        pass
    response = await call_next(request)
    try:
        response.headers["Content-Language"] = lang
    except Exception:
        pass
    return response


# Correlation ID middleware: attach per-request correlation and trace headers


@app.middleware("http")
async def _correlation_headers(request, call_next):  # type: ignore[no-redef]
    try:
        import uuid as _uuid

        corr = request.headers.get("X-Correlation-ID") or _uuid.uuid4().hex
        try:
            request.state.correlation_id = corr  # type: ignore[attr-defined]
        except Exception:
            pass
        response = await call_next(request)
        try:
            response.headers.setdefault("X-Correlation-ID", corr)
            response.headers.setdefault(
                "X-CERTEUS-PCO-correlation.correlation_id", corr
            )
            # Optional simple trace id mirror
            response.headers.setdefault("X-Trace-Id", corr)
        except Exception:
            pass
        return response
    except Exception:
        return await call_next(request)


# Request duration metrics middleware - refined version is defined at the end of file


# Cache OpenAPI JSON in-memory to reduce per-request overhead
_openapi_schema_cache = None


def _cached_openapi():  # type: ignore[override]
    global _openapi_schema_cache
    if _openapi_schema_cache:
        return _openapi_schema_cache
    _openapi_schema_cache = get_openapi(
        title=APP_TITLE,
        version=APP_VERSION,
        routes=app.routes,
    )
    # Enrich with compatibility metadata and docs pointers (W15 D71)
    try:
        info = _openapi_schema_cache.setdefault("info", {})
        info.setdefault("x-release", APP_RELEASE)
        info.setdefault(
            "x-compat",
            {
                "semver": APP_VERSION,
                "status": "rc" if "-" in APP_RELEASE else "stable",
            },
        )
        _openapi_schema_cache.setdefault(
            "externalDocs",
            {
                "description": "Additional resources (endpoints, cURL, runbooks)",
                "url": "https://github.com/CERTEUS/certeus/tree/main/docs",
            },
        )
        public_url = os.getenv("PUBLIC_BASE_URL") or "http://127.0.0.1:8000"
        _openapi_schema_cache.setdefault("servers", [{"url": public_url}])
        # Advertise SDK locations in tree (not runtime-coupled)
        info.setdefault(
            "x-clients",
            {
                "python": "clients/python/certeus_sdk",
                "typescript": "clients/typescript/certeus-sdk",
                "go": "clients/go/certeus",
            },
        )
    except Exception:
        # Never break endpoint due to cosmetics
        pass
    return _openapi_schema_cache


app.openapi = _cached_openapi  # type: ignore[assignment]

# --- blok --- Rejestr routerów -------------------------------------------------

app.include_router(system.router)
app.include_router(preview.router)
if pco_public is not None:
    app.include_router(pco_public.router)
if pco_bundle is not None:
    app.include_router(pco_bundle.router)
app.include_router(export.router)
app.include_router(ledger.router)
app.include_router(mismatch.router)
app.include_router(boundary.router)
app.include_router(verify.router)
app.include_router(cfe.router)
app.include_router(qtm.router)
app.include_router(lexenith.router)
app.include_router(devices.router)
app.include_router(dr.router)
app.include_router(upn.router)
app.include_router(lexqft.router)
app.include_router(qoc.router)
app.include_router(chatops.router)
app.include_router(mailops.router)
app.include_router(ethics.router)
app.include_router(fin.router)
if fin_tokens_api is not None:
    app.include_router(fin_tokens_api.router)
app.include_router(billing.router_tokens)
app.include_router(billing.router)
app.include_router(billing_quota.router)
app.include_router(billing_api.router)
app.include_router(packs.router)
app.include_router(jwks_router)
app.include_router(metrics.router)
app.include_router(tee.router)
app.include_router(pfs.router)
app.include_router(p2p.router)
app.include_router(pfs_dht.router)
app.include_router(openapi_docs.router)
app.include_router(marketplace.router)
app.include_router(proofgate_gateway.router)

# ProofGate proxy to expose /v1/proofgate/publish via gateway (OpenAPI doc parity)
# --- blok --- Health i root redirect -------------------------------------------


@app.get("/health")
def health() -> dict[str, object]:
    """PL: Liveness; EN: Liveness."""

    return {"status": "ok", "version": APP_VERSION}


@app.get("/")
def root_redirect() -> RedirectResponse:
    """

    PL: Landing/Demo (W17): przekierowanie na prostą stronę startową.

    EN: Landing/Demo (W17): redirect to a simple landing page.

    """

    return RedirectResponse(url="/app/public/index.html", status_code=307)


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
        from monitoring.metrics_slo import (
            certeus_http_request_duration_ms,
            certeus_http_request_duration_ms_tenant,
            certeus_http_requests_total,
            record_http_observation,
        )
        from services.api_gateway.limits import (
            get_tenant_id,
        )  # lazy import to avoid cycles

        route = request.scope.get("route")
        path_tmpl = getattr(route, "path", request.url.path)
        status = str(getattr(response, "status_code", 0))
        method = request.method
        dur_ms = (_t.perf_counter() - start) * 1000.0
        tenant = get_tenant_id(request)

        # Global histogram (per-path/method/status)
        certeus_http_request_duration_ms.labels(
            path=path_tmpl, method=method, status=status
        ).observe(dur_ms)
        # Per-tenant histogram and counter (W16 SLO per tenant)
        certeus_http_request_duration_ms_tenant.labels(
            tenant=tenant, path=path_tmpl, method=method, status=status
        ).observe(dur_ms)
        certeus_http_requests_total.labels(
            tenant=tenant, path=path_tmpl, method=method, status=status
        ).inc()
        # In-proc quick summary aggregator (for /v1/metrics/summary)
        record_http_observation(path_tmpl, method, status, tenant, dur_ms)

    except Exception:
        # Metrics must be best-effort; never break request flow
        pass

    return response


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
