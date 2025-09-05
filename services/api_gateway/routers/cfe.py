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

import os
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


class LensingFromFinRequest(BaseModel):
    signals: dict[str, float] = Field(default_factory=dict)
    seed: str | None = None


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


_CURV_CACHE_VALUE: CurvatureResponse | None = None
_CURV_CACHE_TS: float = 0.0
_CURV_TTL_S: float = 1.0


@router.get("/curvature", response_model=CurvatureResponse)
async def curvature(response: Response) -> CurvatureResponse:
    """PL/EN: Telemetria CFE (stub) – maksymalna krzywizna (kappa_max).

    Lekki cache in‑memory (TTL=1 s) w celu ograniczenia kosztu serializacji
    i generowania OpenAPI w gorącej ścieżce CI.
    """
    import time as _t

    global _CURV_CACHE_VALUE, _CURV_CACHE_TS
    now = _t.perf_counter()
    if _CURV_CACHE_VALUE is not None and (now - _CURV_CACHE_TS) < _CURV_TTL_S:
        return _CURV_CACHE_VALUE
    val = CurvatureResponse(kappa_max=0.012)
    # Cache headers from env TTL
    try:
        ttl = int(float(os.getenv("CFE_CACHE_TTL_SEC") or 60))
        response.headers["Cache-Control"] = f"public, max-age={ttl}"
        response.headers["X-CERTEUS-CFE-Cache-TTL"] = str(ttl)
    except Exception:
        pass
    _CURV_CACHE_VALUE = val
    _CURV_CACHE_TS = now
    return val


@router.post("/geodesic", response_model=GeodesicResponse)
async def geodesic(req: GeodesicRequest, request: Request, response: Response) -> GeodesicResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    # Placeholder: return deterministic stub values

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

    # PCO headers
    try:
        response.headers["X-CERTEUS-PCO-cfe.horizon_mass"] = str(0.15)
        response.headers["X-CERTEUS-CFE-Locked"] = "true" if locked else "false"
    except Exception:
        pass

    # Record to Ledger (hash of cfe.horizon_mass + locked)
    try:
        from services.ledger_service.ledger import compute_provenance_hash, ledger_service

        payload = {"cfe.horizon_mass": 0.15, "cfe.locked": locked}
        doc_hash = "sha256:" + compute_provenance_hash(payload, include_timestamp=False)
        case_id = req.case or "cfe-case"
        ledger_service.record_input(case_id=case_id, document_hash=doc_hash)
    except Exception:
        pass

    return HorizonResponse(locked=locked, horizon_mass=0.15)


@router.get("/lensing", response_model=LensingResponse)
async def lensing(domain: str | None = None, response: Response = None) -> LensingResponse:
    """PL/EN: Domenowy lensing — mapa wpływów zależna od kontekstu.

    Parametr `domain` jest opcjonalny i pozwala na doprecyzowanie
    kontekstu (np. `LEX`/`FIN`/`MED`/`SEC`/`CODE`). Brak → zachowanie
    domyślne (LEX‑like) kompatybilne z poprzednimi testami.
    """

    lm, crit, d = get_lensing_map(domain)
    # Apply cache headers if response provided
    try:
        ttl = int(float(os.getenv("CFE_CACHE_TTL_SEC") or 60))
        response.headers["Cache-Control"] = f"public, max-age={ttl}"
        response.headers["X-CERTEUS-CFE-Cache-TTL"] = str(ttl)
    except Exception:
        pass
    return LensingResponse(lensing_map=lm, critical_precedents=crit, domain=d)


@router.post("/lensing/from_fin", response_model=LensingResponse)
async def lensing_from_fin(req: LensingFromFinRequest) -> LensingResponse:
    """PL/EN: Buduje mapę lensingu z sygnałów FIN (prosty normalizator).

    - Wejście: `signals` (nazwa->wartość), opcjonalny `seed` (ignorowany w stubie).
    - Wyjście: LensingResponse z `domain="FIN"` oraz kluczem krytycznym jako max.
    """
    sig = {str(k): float(v) for k, v in (req.signals or {}).items()}
    if not sig:
        return LensingResponse(lensing_map={}, critical_precedents=[], domain="FIN")
    # Normalizacja do [0,1] przez podział przez maksimum bezwzględne
    max_abs = max(abs(v) for v in sig.values()) or 1.0
    norm = {k: max(0.0, min(1.0, (v / max_abs) if max_abs else 0.0)) for k, v in sig.items()}
    crit = [max(norm.items(), key=lambda kv: (kv[1], kv[0]))[0]] if norm else []
    return LensingResponse(lensing_map=norm, critical_precedents=crit, domain="FIN")


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


@router.post("/cache/warm")
async def cache_warm(cases: list[str] | None = None) -> dict[str, int | bool]:
    """PL/EN: Lekki warm-up cache (curvature) + ewentualnie preload lensingu.

    Parametr `cases` jest opcjonalny; zwracamy liczbę zadanych przypadków.
    """
    # Warm curvature cache
    global _CURV_CACHE_VALUE, _CURV_CACHE_TS
    _CURV_CACHE_VALUE = None
    _CURV_CACHE_TS = 0.0
    # Set once
    try:
        # prime the cache (dummy response for header setting not required here)
        _ = await curvature(Response())  # type: ignore[misc]
    except Exception:
        pass
    count = len(cases or [])
    try:
        ttl = int(float(os.getenv("CFE_CACHE_TTL_SEC") or 60))
    except Exception:
        ttl = 60
    return {"ok": True, "warmed": int(count), "ttl_sec": ttl}
