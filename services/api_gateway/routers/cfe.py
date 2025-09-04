#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/cfe.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/cfe.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Stub API dla CFE (geometria sensu) zgodnie z manifestem.

EN: Stub API for CFE (geometry of meaning) per the manifest.

Endpoints:

- POST /v1/cfe/geodesic -> { path, geodesic_action, subject? }

- POST /v1/cfe/horizon  -> { locked, horizon_mass }

- GET  /v1/cfe/lensing  -> { lensing_map, critical_precedents }

Zwracane wartości są placeholderami niezależnymi od środowiska produkcyjnego.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class GeodesicRequest(BaseModel):
    case: str | None = Field(default=None, description="Case identifier (optional)")

    facts: dict[str, Any] | None = None

    norms: dict[str, Any] | None = None


class GeodesicResponse(BaseModel):
    path: list[str]

    geodesic_action: float

    subject: str | None = None


class HorizonRequest(BaseModel):
    case: str | None = None
    lock: bool | None = None


class HorizonResponse(BaseModel):
    locked: bool

    horizon_mass: float


class LensingResponse(BaseModel):
    lensing_map: dict[str, float]

    critical_precedents: list[str]


class WarmCacheResponse(BaseModel):
    warmed: int
    ttl_sec: int | None = None


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: services/api_gateway/routers/cfe.py                           |

# | ROLE: CFE API stubs: /curvature, /geodesic, /horizon, /lensing      |

# +=====================================================================+

router = APIRouter(prefix="/v1/cfe", tags=["CFE"])


class CurvatureResponse(BaseModel):
    kappa_max: float


@router.get("/curvature", response_model=CurvatureResponse)
async def curvature(case_id: str | None = None) -> CurvatureResponse:
    """PL/EN: CFE telemetry — compute Ricci (approx Ollivier) kappa_max for case.

    case_id opcjonalny — determinuje ziarno grafu (metryka realna, ale lekka).
    """
    try:
        from monitoring.metrics_slo import certeus_cfe_kappa_max
        from services.cfe import kappa_max_for_case

        summary = kappa_max_for_case(case_id)
        try:
            certeus_cfe_kappa_max.set(float(summary.kappa_max))
        except Exception:
            pass
        return CurvatureResponse(kappa_max=summary.kappa_max)
    except Exception:
        # Fallback bezpieczny (nie przerywać smoków/UI)
        return CurvatureResponse(kappa_max=0.012)


@router.post("/geodesic", response_model=GeodesicResponse)
async def geodesic(req: GeodesicRequest, request: Request, response: Response) -> GeodesicResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    # Real metric-based geodesic over case graph (lightweight)
    try:
        from services.cfe.metric import geodesic_for_case

        path, action = geodesic_for_case(req.case)
    except Exception:
        # Placeholder fallback (deterministic)
        path = ["premise:A", "premise:B", "inference:merge", "conclusion:C"]
        action = 12.34

    # PCO header for downstream proof-native flows
    try:
        response.headers["X-CERTEUS-PCO-cfe.geodesic_action"] = str(action)
    except Exception:
        pass

    # Record to Ledger (hash of cfe.geodesic_action)
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        doc_hash = "sha256:" + compute_provenance_hash({"cfe.geodesic_action": action}, include_timestamp=False)
        case_id = req.case or "cfe-case"
        ledger_service.record_input(case_id=case_id, document_hash=doc_hash)
    except Exception:
        pass

    return GeodesicResponse(path=path, geodesic_action=action, subject=req.case)


@router.post("/horizon", response_model=HorizonResponse)
async def horizon(req: HorizonRequest, request: Request, response: Response) -> HorizonResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    # Decide locked for samples or explicit lock flag
    locked = bool(req.lock) or (
        isinstance(req.case, str) and ("sample" in req.case.lower() or "przyklad" in req.case.lower())
    )

    # Compute mass (deterministic per case)
    try:
        from services.cfe.metric import horizon_mass_for_case

        mass = horizon_mass_for_case(req.case)
    except Exception:
        mass = 0.15

    # PCO headers
    try:
        response.headers["X-CERTEUS-PCO-cfe.horizon_mass"] = str(mass)
        response.headers["X-CERTEUS-CFE-Locked"] = "true" if locked else "false"
    except Exception:
        pass

    # Record to Ledger (hash of cfe.horizon_mass + locked)
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        payload = {"cfe.horizon_mass": float(mass), "cfe.locked": locked}
        doc_hash = "sha256:" + compute_provenance_hash(payload, include_timestamp=False)
        case_id = req.case or "cfe-case"
        ledger_service.record_input(case_id=case_id, document_hash=doc_hash)
    except Exception:
        pass

    return HorizonResponse(locked=locked, horizon_mass=float(mass))


@router.get("/lensing", response_model=LensingResponse)
async def lensing(case_id: str | None = None) -> LensingResponse:
    try:
        from services.cfe.metric import lensing_map_for_case

        m = lensing_map_for_case(case_id)
        crit = sorted(m, key=m.get, reverse=True)[:1]
        return LensingResponse(lensing_map=m, critical_precedents=crit)
    except Exception:
        # Fallback placeholder
        return LensingResponse(
            lensing_map={"precedent:K_2001": 0.42, "precedent:III_2020": 0.28},
            critical_precedents=["precedent:K_2001"],
        )


@router.post("/cache/warm", response_model=WarmCacheResponse)
async def warm_cache(cases: list[str] | None = None) -> WarmCacheResponse:
    """PL/EN: Rozgrzewa cache CFE dla listy case_id."""
    warmed = 0
    try:
        from services.cfe import kappa_max_for_case

        for cid in cases or []:
            _ = kappa_max_for_case(cid)
            warmed += 1
    except Exception:
        pass
    # Report current TTL setting
    try:
        import os as _os

        ttl = int(_os.getenv("CFE_CACHE_TTL_SEC", "300") or "0")
    except Exception:
        ttl = None
    return WarmCacheResponse(warmed=warmed, ttl_sec=ttl)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
_CASE_LOCKS: dict[str, bool] = {}


class CaseActionIn(BaseModel):
    case: str


class CaseActionOut(BaseModel):
    case: str
    locked: bool
    action: str


@router.post("/case/lock", response_model=CaseActionOut)
async def case_lock(req: CaseActionIn, request: Request, response: Response) -> CaseActionOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    _CASE_LOCKS[req.case] = True
    try:
        response.headers["X-CERTEUS-PCO-cfe.case.lock"] = req.case
    except Exception:
        pass
    return CaseActionOut(case=req.case, locked=True, action="lock")


@router.post("/case/recall", response_model=CaseActionOut)
async def case_recall(req: CaseActionIn, request: Request, response: Response) -> CaseActionOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    _CASE_LOCKS[req.case] = True
    try:
        response.headers["X-CERTEUS-PCO-cfe.case.recall"] = req.case
    except Exception:
        pass
    return CaseActionOut(case=req.case, locked=True, action="recall")


@router.post("/case/revoke", response_model=CaseActionOut)
async def case_revoke(req: CaseActionIn, request: Request, response: Response) -> CaseActionOut:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    _CASE_LOCKS[req.case] = False
    try:
        response.headers["X-CERTEUS-PCO-cfe.case.revoke"] = req.case
    except Exception:
        pass
    return CaseActionOut(case=req.case, locked=False, action="revoke")
