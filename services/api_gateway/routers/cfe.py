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
async def curvature() -> CurvatureResponse:
    """PL/EN: Telemetria CFE (stub) – maksymalna krzywizna (kappa_max)."""
    # Stub: stała wartość, wykorzystywana przez gate'y/telemetrię
    return CurvatureResponse(kappa_max=0.012)


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
async def lensing(domain: str | None = None) -> LensingResponse:
    """PL/EN: Domenowy lensing — mapa wpływów zależna od kontekstu.

    Parametr `domain` jest opcjonalny i pozwala na doprecyzowanie
    kontekstu (np. `LEX`/`FIN`/`MED`/`SEC`/`CODE`). Brak → zachowanie
    domyślne (LEX‑like) kompatybilne z poprzednimi testami.
    """

    lm, crit, d = get_lensing_map(domain)
    return LensingResponse(lensing_map=lm, critical_precedents=crit, domain=d)


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
