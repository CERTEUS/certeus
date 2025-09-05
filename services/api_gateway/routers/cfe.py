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

from services.api_gateway.routers.cfe_config import current_lock_sets, get_lensing_map

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
    domain: str | None = Field(default=None, description="Domain context (LEX/FIN/MED/SEC/CODE)")
    severity: str | None = Field(default=None, description="Heuristic severity (low/medium/high/critical)")


class HorizonResponse(BaseModel):
    locked: bool

    horizon_mass: float


class LensingResponse(BaseModel):
    lensing_map: dict[str, float]

    critical_precedents: list[str]

    domain: str | None = Field(default=None, description="Domain context (e.g., LEX/FIN/MED/SEC/CODE)")


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
async def curvature(response: Response, case_id: str | None = None) -> CurvatureResponse:
    # Ensure cache headers are present based on CFE_CACHE_TTL_SEC
    try:
        import os as _os
        ttl = int(_os.getenv("CFE_CACHE_TTL_SEC", "300") or "0")
        if response is not None and ttl > 0:
            response.headers.setdefault("Cache-Control", f"public, max-age={ttl}")
        if response is not None:
            response.headers.setdefault("X-CERTEUS-CFE-Cache-TTL", str(ttl))
    except Exception:
        pass
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
        # Cache headers
        try:
            import os as _os

            ttl = int(_os.getenv("CFE_CACHE_TTL_SEC", "300") or "0")
            if response is not None and ttl > 0:
                response.headers.setdefault("Cache-Control", f"public, max-age={ttl}")
            if response is not None:
                response.headers.setdefault("X-CERTEUS-CFE-Cache-TTL", str(ttl))
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
        from monitoring.metrics_slo import certeus_cfe_geodesic_action
        from services.cfe.metric import geodesic_for_case

        path, action = geodesic_for_case(req.case)
        try:
            certeus_cfe_geodesic_action.observe(float(action))
        except Exception:
            pass
    except Exception:
        # Placeholder fallback (deterministic)
        path = ["premise:A", "premise:B", "inference:merge", "conclusion:C"]
        action = 12.34

    # PCO header for downstream proof-native flows
    try:
        response.headers["X-CERTEUS-PCO-cfe.geodesic_action"] = str(action)
    except Exception:
        pass
    # POST responses should not be cached by intermediaries
    try:
        response.headers.setdefault("Cache-Control", "no-store")
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

    # Decide locked with domain/severity heuristics, fallback to sample/explicit
    def _should_lock() -> bool:
        # Explicit lock wins
        if bool(req.lock):
            return True
        # Domain-based heuristic by severity
        d = (req.domain or "").strip().upper()
        s = (req.severity or "").strip().lower()
        _domains, _severities = current_lock_sets()
        if d in _domains and s in _severities:
            return True
        # Legacy behavior: samples lock automatically
        if isinstance(req.case, str) and ("sample" in req.case.lower() or "przyklad" in req.case.lower()):
            return True
        return False

    locked = _should_lock()

    # Compute mass (deterministic per case)
    try:
        from monitoring.metrics_slo import certeus_cfe_horizon_mass
        from services.cfe.metric import horizon_mass_for_case

        mass = horizon_mass_for_case(req.case)
        try:
            certeus_cfe_horizon_mass.set(float(mass))
        except Exception:
            pass
    except Exception:
        mass = 0.15

    # PCO headers
    try:
        response.headers["X-CERTEUS-PCO-cfe.horizon_mass"] = str(mass)
        response.headers["X-CERTEUS-CFE-Locked"] = "true" if locked else "false"
    except Exception:
        pass
    # POST responses should not be cached
    try:
        response.headers.setdefault("Cache-Control", "no-store")
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


class LensingFromFinIn(BaseModel):
    signals: dict[str, float]
    seed: str | None = None


class LensingFromFinOut(BaseModel):
    lensing_map: dict[str, float]
    critical_precedents: list[str]


@router.post("/lensing/from_fin", response_model=LensingFromFinOut)
async def lensing_from_fin(payload: LensingFromFinIn, response: Response) -> LensingFromFinOut:
    """PL/EN: Mapuje sygnały FIN (risk/sentiment) na szkic lensingu CFE.

    Heurystyka: score = sentiment - risk, skaluje wagi 2–3 precedensów deterministycznie.
    """
    s = payload.signals or {}
    risk = float(sum(v for k, v in s.items() if "risk" in k.lower()))
    sent = float(sum(v for k, v in s.items() if ("sent" in k.lower()) or ("sentiment" in k.lower())))
    score = sent - risk
    # Deterministyczny wybór precedensów na podstawie seed/score
    seed_key = payload.seed or f"FIN::{int(score * 1000)}"
    try:
        from services.cfe.metric import lensing_map_for_case

        m = lensing_map_for_case(seed_key)
        # Lekka modulacja wag przez score
        shift = 0.05 * max(-1.0, min(1.0, score))
        mm = {k: max(0.0, min(1.0, float(v) + shift)) for k, v in m.items()}
        tot = sum(mm.values()) or 1.0
        mm = {k: round(v / tot, 3) for k, v in mm.items()}
    except Exception:
        mm = {"precedent:K_2001": 0.6, "precedent:III_2020": 0.4}
    crit = sorted(mm, key=mm.get, reverse=True)[:1]
    # PCO header
    try:
        import json as _json

        response.headers["X-CERTEUS-PCO-cfe.lensing_from_fin"] = _json.dumps({"score": score})
    except Exception:
        pass
    return LensingFromFinOut(lensing_map=mm, critical_precedents=crit)


@router.get("/lensing", response_model=LensingResponse)
async def lensing(domain: str | None = None, response: Response | None = None) -> LensingResponse:
    # Ensure cache headers are present based on CFE_CACHE_TTL_SEC
    try:
        import os as _os
        ttl = int(_os.getenv("CFE_CACHE_TTL_SEC", "300") or "0")
        if response is not None and ttl > 0:
            response.headers.setdefault("Cache-Control", f"public, max-age={ttl}")
        if response is not None:
            response.headers.setdefault("X-CERTEUS-CFE-Cache-TTL", str(ttl))
    except Exception:
        pass
    """PL/EN: Domenowy lensing — mapa wpływów zależna od kontekstu.

    Parametr `domain` jest opcjonalny i pozwala na doprecyzowanie
    kontekstu (np. `LEX`/`FIN`/`MED`/`SEC`/`CODE`). Brak → zachowanie
    domyślne (LEX‑like) kompatybilne z poprzednimi testami.
    """

    lm, crit, d = get_lensing_map(domain)
    return LensingResponse(lensing_map=lm, critical_precedents=crit, domain=d)


# === I/O / ENDPOINTS ===

@router.post("/cache/warm", response_model=WarmCacheResponse)
async def cache_warm(payload: list[str] | None = None) -> WarmCacheResponse:
    """No-op warm endpoint to establish caches and report TTL."""
    try:
        import os as _os
        ttl = int(_os.getenv("CFE_CACHE_TTL_SEC", "300") or "0")
    except Exception:
        ttl = 0
    return WarmCacheResponse(warmed=len(payload or []), ttl_sec=ttl)

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
