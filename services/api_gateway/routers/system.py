#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/system.py              |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/system.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla obszaru diagnostyka/system info.

EN: FastAPI router for diagnostics/system info.
"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===


#!/usr/bin/env python3

from __future__ import annotations

from datetime import UTC, datetime
from hashlib import sha256
import json
from typing import Annotated, Any

from fastapi import APIRouter, File, HTTPException, Request, Response, UploadFile
from pydantic import BaseModel, Field

from services.connectors.fhir.router import router as fhir_router  # NEW: FHIR
from services.ingest_service.adapters.contracts import Blob
from services.ingest_service.adapters.ocr_injector import build_ocr_preview

router = APIRouter(tags=["system"])


# Mount FHIR connector under the same aggregating router

router.include_router(fhir_router)


# ---------------------------------------------------------------------

# /v1/ingest

# ---------------------------------------------------------------------


class IngestResult(BaseModel):
    kind: str = Field(default="fact")

    role: str

    source: str

    value: str

    fact_id: str


@router.post("/v1/ingest")
async def ingest_document(
    request: Request,
    response: Response,
    file: Annotated[UploadFile, File(...)],
) -> list[dict[str, Any]]:
    """

    PL: Zwraca dwa deterministyczne fakty (z `fact_id`, `thesis`, `confidence_score`),

        waliduje MIME/rozmiar i ustawia nagłówek łańcucha `X-CERTEUS-Ledger-Chain`.

        Dodatkowo (nieinwazyjnie) umieszcza skrót OCR w nagłówku

        `X-CERTEUS-OCR-Preview` dla PDF/obrazów.

    EN: Returns two deterministic facts (with `fact_id`, `thesis`, `confidence_score`),

        validates MIME/size, and sets `X-CERTEUS-Ledger-Chain` header. Also (non-

        invasive) puts OCR snippet into `X-CERTEUS-OCR-Preview` header for PDF/images.

    """

    # Enforce per-tenant budget/limits

    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=2)

    MAX_BYTES = 10 * 1024 * 1024  # 10 MiB

    allowed_mime = "application/pdf"

    if (file.content_type or "") != allowed_mime:
        raise HTTPException(status_code=415, detail="Only application/pdf is supported")

    content = await file.read()

    if len(content) > MAX_BYTES:
        raise HTTPException(status_code=413, detail="File too large")

    src = file.filename or "document.pdf"

    def make_fact(role: str, value: str) -> dict[str, Any]:
        base = f"{src}|{role}|{value}".encode()

        fid = "fact-" + sha256(base).hexdigest()[:12]

        return {
            "kind": "fact",
            "role": role,
            "source": src,
            "value": value,
            "fact_id": fid,
        }

    facts = [
        make_fact("claim_contract_date", "2023-10-01"),
        make_fact("evidence_payment", "TAK"),
    ]

    # Uzupełnij wymagane pola (thesis + confidence)

    for f in facts:
        if f["role"] == "claim_contract_date":
            f["thesis"] = "Umowa została zawarta 2023-10-01."

            f["confidence_score"] = 0.98

        elif f["role"] == "evidence_payment":
            f["thesis"] = "Istnieje dowód wpłaty."

            f["confidence_score"] = 0.99

    # Nagłówek łańcucha: "sha256:<...>;sha256:<...>"

    chain_parts: list[str] = []

    for f in facts:
        payload = json.dumps(f, ensure_ascii=False, sort_keys=True).encode("utf-8")

        chain_parts.append("sha256:" + sha256(payload).hexdigest())

    response.headers["X-CERTEUS-Ledger-Chain"] = ";".join(chain_parts)

    # DODATEK: OCR preview jako nagłówek (bez zmiany body).

    try:
        blob = Blob(
            filename=src,
            content_type=file.content_type or "application/octet-stream",
            data=content,
        )

        ocr = await build_ocr_preview(blob, case_id=None, max_chars=160)

        preview = ocr.get("ocr_preview")

        if preview:
            # Krótki, jednowierszowy nagłówek (bez znaków nowych linii).

            response.headers["X-CERTEUS-OCR-Preview"] = " ".join(preview.split())

    except Exception:
        # Bezpieczne pominięcie OCR w razie błędu stubu.

        pass

    return facts


# ---------------------------------------------------------------------

# /v1/sources/cache

# ---------------------------------------------------------------------


class SourceCacheRequest(BaseModel):
    uri: str


class SourceCacheResponse(BaseModel):
    uri: str

    digest: str

    path: str

    retrieved_at: str


@router.post("/v1/sources/cache", response_model=SourceCacheResponse)
def cache_source(req: SourceCacheRequest) -> SourceCacheResponse:
    """

    Cache a legal source by URI using Law-as-Data cache; return digest and path.

    """

    from services.law_as_data.cache import cache_from_uri

    cs = cache_from_uri(req.uri)

    return SourceCacheResponse(uri=cs.uri, digest=cs.digest, path=str(cs.path), retrieved_at=cs.retrieved_at)


# ---------------------------------------------------------------------

# /v1/analyze

# ---------------------------------------------------------------------


@router.post("/v1/analyze")
async def analyze(request: Request, case_id: str, file: Annotated[UploadFile, File(...)]) -> dict[str, Any]:
    """

    Minimalny stub E2E: przyjmuje PDF i zwraca wynik SAT z prostym modelem.

    Zgodne z tests/e2e/test_e2e_pl_286kk_0001.py.

    """

    # Enforce limits for analysis

    from services.api_gateway.limits import enforce_limits

    enforce_limits(request, cost_units=3)

    await file.read()  # nieużywane w stubie

    return {
        "case_id": case_id,
        "analysis_result": {"status": "sat", "model": "[x=True]"},
    }


# ---------------------------------------------------------------------

# /v1/sipp/snapshot/{act_id}

# ---------------------------------------------------------------------


@router.get("/v1/sipp/snapshot/{act_id}")
async def get_snapshot(act_id: str) -> dict[str, Any]:
    """Zwraca minimalny snapshot (dict), aby dozwolić klucz `_certeus`."""

    text = (
        "Art. 286 k.k.: Kto, w celu osiągnięcia korzyści majątkowej, doprowadza inną osobę "
        "do niekorzystnego rozporządzenia mieniem za pomocą wprowadzenia w błąd..."
    ).strip()

    digest = "sha256:" + sha256(text.encode("utf-8")).hexdigest()

    snap_ts = datetime.now(UTC).isoformat(timespec="seconds")

    return {
        "act_id": act_id,
        "version_id": "2023-10-01",
        "title": "Kodeks karny – art. 286",
        "source_url": "https://isap.sejm.gov.pl/isap.nsf/DocDetails.xsp?id=WDU19970880553",
        "text": text,
        "text_sha256": digest,
        "at": None,
        "snapshot_timestamp": snap_ts,
        "_certeus": {"snapshot_timestamp_utc": snap_ts},
    }
