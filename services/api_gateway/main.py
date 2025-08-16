# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/main.py                          |
# | ROLE: FastAPI application wiring public routers & /health.  |
# | PLIK: services/api_gateway/main.py                          |
# | ROLA: Aplikacja FastAPI spinająca routery publiczne i       |
# |       /health, z endpointem /v1/ingest oraz Ledger headerem |
# +-------------------------------------------------------------+

"""
PL: Główna aplikacja API CERTEUS. Definiuje obiekt `app`, dołącza routery
    (w tym /v1/verify), udostępnia /health oraz endpoint /v1/ingest
    (OCR→FACTLOG) z rejestracją chain-of-custody (Ledger) eksponowaną
    w nagłówku `X-CERTEUS-Ledger-Chain`.

EN: CERTEUS main API app. Defines `app`, attaches routers (incl. /v1/verify),
    exposes /health and /v1/ingest (OCR→FACTLOG), and records chain-of-custody
    (Ledger) returned via `X-CERTEUS-Ledger-Chain` header.
"""

# [BLOCK: IMPORTS]
from __future__ import annotations

import asyncio
import json
from datetime import date
from typing import List, Optional, Annotated

from fastapi import FastAPI, File, HTTPException, Response, UploadFile, Query

from services.ingest_service.factlog_mapper import FactlogMapper
from services.ingest_service.models import Fact
from services.ingest_service.ocr_pipeline import OcrPipeline
from services.ledger_service.ledger import Ledger

# === SIPP Indexer imports ===
from services.sipp_indexer_service.isap_adapter import IsapAdapter
from services.sipp_indexer_service.models import LegalActSnapshot

# === SIPP Indexer init ===
isap_adapter = IsapAdapter()

# [BLOCK: APP]
app = FastAPI(title="CERTEUS API", version="1.0")

# [BLOCK: INGEST INIT]
ocr_pipeline = OcrPipeline()
factlog_mapper = FactlogMapper()
ledger = Ledger()

# [BLOCK: CONSTANTS]
ALLOWED_MIME = {"application/pdf", "text/plain", "image/png", "image/jpeg"}
MAX_BYTES = 10 * 1024 * 1024  # 10 MB
LEDGER_HEADER = "X-CERTEUS-Ledger-Chain"


# [BLOCK: ENDPOINT • /v1/ingest]
@app.post("/v1/ingest", response_model=List[Fact], tags=["Ingestion Service"])
async def ingest_document(
    response: Response, file: UploadFile = File(...)
) -> list[Fact]:
    """
    PL: Przyjmuje dokument, uruchamia OCR (stub) i mapowanie FACTLOG.
        Dodatkowo rejestruje chain-of-custody w Ledger i zwraca go w nagłówku:
        X-CERTEUS-Ledger-Chain: sha256:...;sha256:...;sha256:...

    EN: Accepts a document, runs OCR (stub) and FACTLOG mapping.
        Additionally records chain-of-custody in Ledger and exposes via header:
        X-CERTEUS-Ledger-Chain: sha256:...;sha256:...;sha256:...
    """
    if file.content_type not in ALLOWED_MIME:
        raise HTTPException(status_code=415, detail="Unsupported media type")

    data = await file.read()
    if len(data) > MAX_BYTES:
        raise HTTPException(status_code=413, detail="File too large")

    # [BLOCK: LEDGER • INPUT]
    input_rec = ledger.record_input(data, stage="input")

    # [BLOCK: OCR]
    try:
        ocr_output = await asyncio.wait_for(
            asyncio.to_thread(ocr_pipeline.process_document, data),
            timeout=15,
        )
    except asyncio.TimeoutError:
        raise HTTPException(status_code=504, detail="OCR timeout") from None

    # [BLOCK: LEDGER • OCR RESULT]
    ocr_bytes = json.dumps(ocr_output, ensure_ascii=False, sort_keys=True).encode(
        "utf-8"
    )
    ocr_rec = ledger.record_transform(input_rec, ocr_bytes, stage="ocr")

    # [BLOCK: MAP → FACTS]
    facts = factlog_mapper.map_to_facts(ocr_output, data)

    # [BLOCK: LEDGER • FACTS EXPORT]
    facts_payload = json.dumps(
        [
            f.model_dump(mode="json", exclude_none=True) for f in facts
        ],  # ⟵ było: model_dump(exclude_none=True)
        ensure_ascii=False,
        sort_keys=True,
    ).encode("utf-8")
    last_rec = ledger.record_export(ocr_rec, facts_payload)

    # [BLOCK: LEDGER • EXPOSE HEADER]
    chain_ids = ledger.ancestry(last_rec.id)  # [root .. last]
    response.headers[LEDGER_HEADER] = ";".join(chain_ids)

    return facts


# [BLOCK: HEALTH]
@app.get("/health")
def health() -> dict[str, bool]:
    """PL/EN: Liveness check."""
    return {"ok": True}


# [BLOCK: ROUTERS IMPORTS]
# Required by Day 5: /v1/verify
from services.api_gateway.routers.verify import router as verify_router  # noqa: E402

# Optional routers (if present in repo)
try:  # noqa: E402
    from services.api_gateway.routers.system import router as system_router  # type: ignore
except Exception:  # pragma: no cover
    system_router = None  # type: ignore

try:  # noqa: E402
    from services.api_gateway.routers.export import router as export_router  # type: ignore
except Exception:  # pragma: no cover
    export_router = None  # type: ignore

try:  # noqa: E402
    from services.api_gateway.routers.ledger import router as ledger_router  # type: ignore
except Exception:  # pragma: no cover
    ledger_router = None  # type: ignore


# [BLOCK: ROUTER REGISTRATION]
app.include_router(verify_router)
if system_router is not None:
    app.include_router(system_router)
if export_router is not None:
    app.include_router(export_router)
if ledger_router is not None:
    app.include_router(ledger_router)
if __name__ == "__main__":
    import uvicorn

    uvicorn.run(
        "services.api_gateway.main:app", host="127.0.0.1", port=8000, reload=True
    )


# === SIPP Indexer Service Endpoints ===
@app.get(
    "/v1/sipp/snapshot/{act_id}",
    response_model=LegalActSnapshot,
    tags=["SIPP Indexer Service"],
)
def get_legal_act_snapshot(
    act_id: str,
    at: Annotated[
        Optional[date], Query(description="Date for which snapshot is requested")
    ] = None,
) -> LegalActSnapshot:
    try:
        return isap_adapter.fetch_act_snapshot(act_id, at=at)
    except Exception as exc:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Snapshot error: {exc}")
