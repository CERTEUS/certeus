#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/lexenith.py            |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/lexenith.py            |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla LEXENITH v0.1: Micro‑Court/Motion generator, CLDF
    renormalizacja oraz Why‑Not (PCΔ) eksport.

EN: FastAPI router for LEXENITH v0.1: Micro‑Court/Motion generator, CLDF
    renormalization and Why‑Not (PCΔ) export.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import hashlib
import json
from typing import Any

from fastapi import APIRouter, Request, Response
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class MotionRequest(BaseModel):
    case_id: str
    pattern_id: str = Field(pattern=r"^(motion-dismiss|motion-summary)$")
    facts: dict[str, Any] | None = None
    citations: list[str] = Field(default_factory=list)


class MotionResponse(BaseModel):
    document: str
    citations: list[dict[str, str]]


class CitationItem(BaseModel):
    text: str
    weight: float = 1.0


class CLDFRequest(BaseModel):
    citations: list[CitationItem]
    damping: float | None = Field(default=None, ge=0.0, le=1.0)


class CLDFResponse(BaseModel):
    citations: list[dict[str, Any]]
    normalized: bool


class WhyNotRequest(BaseModel):
    claim: str
    counter_arguments: list[str]


class WhyNotResponse(BaseModel):
    ok: bool
    trace_uri: str


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/lexenith", tags=["lexenith"])

_MOTIONS: dict[str, str] = {
    "motion-dismiss": (
        "Wniosek o oddalenie\n\n"
        "Sądzie, wnoszę o oddalenie powództwa z uwagi na brak podstaw prawnych oraz brak wykazania szkody."
    ),
    "motion-summary": (
        "Wniosek o rozstrzygnięcie na posiedzeniu niejawnym\n\n"
        "Sądzie, wnoszę o wydanie wyroku na posiedzeniu niejawnym wobec jasnego stanu faktycznego i prawnego."
    ),
}


def _hash_text(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


@router.post("/motion/generate", response_model=MotionResponse)
async def motion_generate(req: MotionRequest, request: Request, response: Response) -> MotionResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    body = _MOTIONS.get(req.pattern_id, _MOTIONS["motion-dismiss"])
    facts = req.facts or {}

    doc = body + "\n\nFakty (skrót):\n" + json.dumps(facts, ensure_ascii=False, indent=2)

    cites: list[dict[str, str]] = []
    for c in req.citations:
        h = _hash_text(c)
        cites.append({"text": c, "hash": h, "uri": f"hash://sha256/{h}"})

    # PCO: nagłówek z cytatami (hash/uri)
    try:
        response.headers["X-CERTEUS-PCO-lex.motion.citations"] = json.dumps(cites, separators=(",", ":"))
    except Exception:
        pass

    return MotionResponse(document=doc, citations=cites)


@router.post("/cldf/renormalize", response_model=CLDFResponse)
async def cldf_renormalize(req: CLDFRequest, request: Request) -> CLDFResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    items = req.citations
    s = sum(max(0.0, it.weight) for it in items) or 1.0
    damping = float(req.damping) if req.damping is not None else 1.0
    out: list[dict[str, Any]] = []
    for it in items:
        w = max(0.0, it.weight)
        p = (w / s) * damping
        h = _hash_text(it.text)
        out.append({"text": it.text, "hash": h, "authority_score": round(p, 6)})
    return CLDFResponse(citations=out, normalized=True)


@router.post("/why_not/export", response_model=WhyNotResponse)
async def why_not_export(req: WhyNotRequest, request: Request) -> WhyNotResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)

    payload = {"claim": req.claim, "counter_arguments": req.counter_arguments}
    h = _hash_text(json.dumps(payload, ensure_ascii=False, sort_keys=True))
    trace_uri = f"pfs://why-not/{h}"
    return WhyNotResponse(ok=True, trace_uri=trace_uri)


# --- W6: Micro‑Court — pipeline lock → publish (PCO ścieżki) ------------------


class MicroCourtLockRequest(BaseModel):
    case_id: str


class MicroCourtLockResponse(BaseModel):
    ok: bool
    case_id: str
    locked: bool
    pco: dict | None = None


class MicroCourtPublishRequest(BaseModel):
    case_id: str
    footnotes: list[str] | None = None


class MicroCourtPublishResponse(BaseModel):
    ok: bool
    case_id: str
    published: bool
    path: list[dict[str, str]]
    pco: dict | None = None


_LOCKS: dict[str, bool] = {}
_CASEBOOK: list[dict[str, Any]] = []  # newest-first entries: {case_id, path}


@router.post("/micro_court/lock", response_model=MicroCourtLockResponse)
async def micro_court_lock(req: MicroCourtLockRequest, request: Request, response: Response) -> MicroCourtLockResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    case = req.case_id.strip()
    _LOCKS[case] = True
    tenant = get_tenant_id(request)

    path_step = {"step": "lock", "by": tenant}
    pco = {"lex.micro_court.path": [path_step]}

    # Metryki + PCO nagłówek
    try:
        from monitoring.metrics_slo import certeus_lex_micro_court_locked_total

        certeus_lex_micro_court_locked_total.labels(case=case, tenant=tenant).inc()
    except Exception:
        pass
    try:
        response.headers["X-CERTEUS-PCO-lex.micro_court"] = json.dumps(
            pco["lex.micro_court.path"], separators=(",", ":")
        )
    except Exception:
        pass
    return MicroCourtLockResponse(ok=True, case_id=case, locked=True, pco=pco)


@router.post("/micro_court/publish", response_model=MicroCourtPublishResponse)
async def micro_court_publish(
    req: MicroCourtPublishRequest, request: Request, response: Response
) -> MicroCourtPublishResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=2)
    case = req.case_id.strip()
    tenant = get_tenant_id(request)
    locked = bool(_LOCKS.get(case, False))

    # Konstruuj ścieżkę Micro‑Court: lock → publish (+footnotes)
    path: list[dict[str, str]] = []
    if locked:
        path.append({"step": "lock", "by": tenant})
    path.append({"step": "publish", "by": tenant})
    for i, note in enumerate(req.footnotes or []):
        try:
            h = _hash_text(note)
            path.append({"step": f"fn#{i + 1}", "hash": h})
        except Exception:
            pass

    pco = {"lex.micro_court.path": path}

    # Ledger zapis (hash PCO) – best‑effort
    try:
        from services.ledger_service.ledger import (
            compute_provenance_hash,
            ledger_service,
        )

        doc_hash = "sha256:" + compute_provenance_hash(pco, include_timestamp=False)
        ledger_service.record_input(case_id=case, document_hash=doc_hash)
    except Exception:
        pass

    # Metryki + PCO nagłówek
    try:
        from monitoring.metrics_slo import certeus_lex_micro_court_published_total

        certeus_lex_micro_court_published_total.labels(case=case, tenant=tenant).inc()
    except Exception:
        pass
    try:
        response.headers["X-CERTEUS-PCO-lex.micro_court"] = json.dumps(
            pco["lex.micro_court.path"], separators=(",", ":")
        )
    except Exception:
        pass
    # Casebook (newest-first)
    try:
        _CASEBOOK.insert(0, {"case_id": case, "path": path})
        if len(_CASEBOOK) > 20:
            del _CASEBOOK[20:]
    except Exception:
        pass
    return MicroCourtPublishResponse(ok=True, case_id=case, published=True, path=path, pco=pco)


# --- Casebook (W12): lista ostatnich spraw Micro‑Court ------------------------


class CasebookEntry(BaseModel):
    case_id: str
    path: list[dict[str, str]]


class CasebookResponse(BaseModel):
    cases: list[CasebookEntry]


@router.get("/casebook", response_model=CasebookResponse)
async def casebook(request: Request) -> CasebookResponse:
    """Zwraca ostatnie sprawy z Micro‑Court (max 10), newest‑first."""
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    # zwróć kopię, newest-first (już utrzymywane newest-first)
    out: list[CasebookEntry] = []
    for it in _CASEBOOK[:10]:
        out.append(CasebookEntry(case_id=str(it.get("case_id") or ""), path=list(it.get("path") or [])))
    return CasebookResponse(cases=out)


# --- Pilot W16: 3 sprawy E2E + feedback ---


class PilotCase(BaseModel):
    case_id: str
    title: str
    status: str


class PilotCasesResponse(BaseModel):
    cases: list[PilotCase]


class PilotFeedbackRequest(BaseModel):
    case_id: str
    rating: int = Field(ge=1, le=5)
    comments: str | None = None


class PilotFeedbackResponse(BaseModel):
    ok: bool
    case_id: str
    rating: int


_PILOT_CASES: list[PilotCase] = [
    PilotCase(
        case_id="LEX-PILOT-001",
        title="Umowa pożyczki — spór o odsetki",
        status="IN_PROGRESS",
    ),
    PilotCase(
        case_id="LEX-PILOT-002",
        title="Odszkodowanie komunikacyjne — regres",
        status="IN_PROGRESS",
    ),
    PilotCase(
        case_id="LEX-PILOT-003",
        title="Naruszenie dóbr osobistych — przeprosiny",
        status="IN_PROGRESS",
    ),
]

_PILOT_FEEDBACK: dict[str, list[int]] = {}


@router.get("/pilot/cases", response_model=PilotCasesResponse)
async def pilot_cases(request: Request) -> PilotCasesResponse:
    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=1)
    return PilotCasesResponse(cases=_PILOT_CASES)


@router.post("/pilot/feedback", response_model=PilotFeedbackResponse)
async def pilot_feedback(req: PilotFeedbackRequest, request: Request, response: Response) -> PilotFeedbackResponse:
    from services.api_gateway.limits import enforce_limits, get_tenant_id

    enforce_limits(request, cost_units=1)
    tenant = get_tenant_id(request)
    rating = int(req.rating)
    _PILOT_FEEDBACK.setdefault(req.case_id, []).append(rating)

    # Metryki + PCO
    try:
        from monitoring.metrics_slo import (
            certeus_lex_pilot_feedback_total,
            certeus_lex_pilot_last_rating,
        )

        certeus_lex_pilot_feedback_total.labels(case=req.case_id, tenant=tenant).inc()
        certeus_lex_pilot_last_rating.labels(case=req.case_id, tenant=tenant).set(float(rating))
    except Exception:
        pass
    try:
        response.headers["X-CERTEUS-PCO-lex.pilot.feedback"] = json.dumps(
            {"case": req.case_id, "rating": rating, "tenant": tenant},
            separators=(",", ":"),
        )
    except Exception:
        pass

    return PilotFeedbackResponse(ok=True, case_id=req.case_id, rating=rating)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
