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


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
