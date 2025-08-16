# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/main.py                          |
# | ROLE: FastAPI application wiring public routers & /health.  |
# | PLIK: services/api_gateway/main.py                          |
# | ROLA: Aplikacja FastAPI spinająca routery publiczne i       |
# |       /health, z /v1/ingest oraz integracją D9/D10.         |
# +-------------------------------------------------------------+

"""
PL: Główna aplikacja API CERTEUS. Definiuje `app`, dołącza routery (w tym
    /v1/verify), udostępnia /health oraz endpointy:
    - /v1/ingest  (OCR → FACTLOG + Ledger header),
    - /v1/analyze (D9: E2E stub – Ingest→LEXLOG→Z3),
    - /v1/export  (D10: Exporter fallback, jeśli brak routera export).

EN: CERTEUS main API app. Defines `app`, attaches routers (incl. /v1/verify),
    exposes /health and endpoints:
    - /v1/ingest  (OCR → FACTLOG + Ledger header),
    - /v1/analyze (D9: E2E stub – Ingest→LEXLOG→Z3),
    - /v1/export  (D10: Exporter fallback if no export router present).
"""

# ======================================================================
# [BLOCK: IMPORTS • CORE]
# ======================================================================
from __future__ import annotations

import asyncio
import json
from datetime import date
from pathlib import Path
from typing import Annotated, Any, Dict, List, Optional, TypedDict, NotRequired

import uvicorn
from fastapi import FastAPI, File, HTTPException, Query, Response, UploadFile

# Ingestion & Ledger
from services.ingest_service.factlog_mapper import FactlogMapper
from services.ingest_service.models import Fact
from services.ingest_service.ocr_pipeline import OcrPipeline
from services.ledger_service.ledger import Ledger

# Day 8/9/10 integration
from services.lexlog_parser.parser import LexlogParser
from kernel.e2e_verifier import DualCoreVerifier
from services.exporter_service.exporter import ExporterService
from pydantic import BaseModel

# SIPP Indexer
from services.sipp_indexer_service.isap_adapter import IsapAdapter
from services.sipp_indexer_service.models import LegalActSnapshot

# Routers (top-of-file to avoid E402)
from services.api_gateway.routers.verify import router as verify_router  # required

try:
    from services.api_gateway.routers.system import router as system_router  # optional
except Exception:  # pragma: no cover
    system_router = None  # type: ignore[assignment]

try:
    from services.api_gateway.routers.export import router as export_router  # optional
except Exception:  # pragma: no cover
    export_router = None  # type: ignore[assignment]

try:
    from services.api_gateway.routers.ledger import router as ledger_router  # optional
except Exception:  # pragma: no cover
    ledger_router = None  # type: ignore[assignment]


# ======================================================================
# [BLOCK: TYPES]
# ======================================================================
class SimpleFactDict(TypedDict, total=False):
    """PL: Minimalny kształt faktu dla translatora (D9).
    EN: Minimal fact shape for translator (D9)."""

    role: str
    value: NotRequired[bool]


# ======================================================================
# [BLOCK: APP & SERVICES INIT]
# ======================================================================
app = FastAPI(title="CERTEUS API", version="1.0")

# Ingestion
ocr_pipeline = OcrPipeline()
factlog_mapper = FactlogMapper()
ledger = Ledger()

# SIPP Indexer
isap_adapter = IsapAdapter()

# Day 8/9/10 components
lexlog_parser = LexlogParser()
verifier = DualCoreVerifier()
exporter_service = ExporterService()

# Constants
ALLOWED_MIME = {"application/pdf", "text/plain", "image/png", "image/jpeg"}
MAX_BYTES = 10 * 1024 * 1024  # 10 MB
LEDGER_HEADER = "X-CERTEUS-Ledger-Chain"


# ======================================================================
# [BLOCK: ENDPOINT • /v1/ingest]
# ======================================================================
@app.post("/v1/ingest", response_model=List[Fact], tags=["Ingestion Service"])
async def ingest_document(
    response: Response, file: UploadFile = File(...)
) -> List[Fact]:
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

    # [LEDGER • INPUT]
    input_rec = ledger.record_input(data, stage="input")

    # [OCR]
    try:
        ocr_output = await asyncio.wait_for(
            asyncio.to_thread(ocr_pipeline.process_document, data), timeout=15
        )
    except asyncio.TimeoutError:
        raise HTTPException(status_code=504, detail="OCR timeout") from None

    # [LEDGER • OCR RESULT]
    ocr_bytes = json.dumps(ocr_output, ensure_ascii=False, sort_keys=True).encode(
        "utf-8"
    )
    ocr_rec = ledger.record_transform(input_rec, ocr_bytes, stage="ocr")

    # [MAP → FACTS]
    facts: List[Fact] = factlog_mapper.map_to_facts(ocr_output, data)

    # [LEDGER • FACTS EXPORT]
    facts_payload = json.dumps(
        [f.model_dump(mode="json", exclude_none=True) for f in facts],
        ensure_ascii=False,
        sort_keys=True,
    ).encode("utf-8")
    last_rec = ledger.record_export(ocr_rec, facts_payload)

    # [LEDGER • EXPOSE HEADER]
    chain_ids = ledger.ancestry(last_rec.id)  # [root .. last]
    response.headers[LEDGER_HEADER] = ";".join(chain_ids)

    return facts


# ======================================================================
# [BLOCK: ENDPOINT • /v1/analyze]  (D9 – Orchestration)
# ======================================================================
@app.post("/v1/analyze", tags=["Orchestration"])
async def analyze_case(
    case_id: str,
    file: UploadFile = File(...),
) -> Dict[str, Any]:
    """
    PL: E2E (stub): Ingest (stub) → Parsowanie LEXLOG → Weryfikacja Z3.
    EN: E2E (stub): Ingest (stub) → LEXLOG parsing → Z3 verification.
    """
    # Consume the file (not used by stub ingest yet)
    await file.read()

    # [STUB INGEST] – translator akceptuje Mapping z kluczem 'role'
    facts: List[SimpleFactDict] = [
        {"role": "intent_financial_gain", "value": True},
        {"role": "act_deception", "value": True},
        {"role": "detrimental_property_disposal", "value": True},
    ]

    # [LOAD & PARSE RULES]
    rules_path = Path("packs/jurisdictions/PL/rules/kk.lex")
    rules_content = rules_path.read_text(encoding="utf-8")
    parsed_rule: Dict[str, Any] = lexlog_parser.parse(rules_content)

    # [VERIFY]
    result: Dict[str, Any] = verifier.analyze_case(facts, parsed_rule)

    return {"case_id": case_id, "analysis_result": result}


# ======================================================================
# [BLOCK: ENDPOINT • /v1/export]  (D10 – fallback if no export router)
# ======================================================================
class ExportRequest(BaseModel):
    """PL: DTO żądania eksportu. EN: Export request DTO."""

    case_id: str
    analysis_result: Dict[str, Any]


if export_router is None:  # only if no dedicated export router is present

    @app.post("/v1/export", tags=["Exporter Service"])
    def export_analysis_report(request: ExportRequest) -> Dict[str, Any]:
        """
        PL: Generuje raport tekstowy na bazie szablonu i danych analizy.
        EN: Generates a text report based on the template and analysis data.
        """
        out_path: Path = exporter_service.export_report(
            request.case_id, request.analysis_result
        )
        return {"message": "Report generated successfully", "path": str(out_path)}


# ======================================================================
# [BLOCK: HEALTH]
# ======================================================================
@app.get("/health")
def health() -> Dict[str, bool]:
    """PL/EN: Liveness check."""
    return {"ok": True}


# ======================================================================
# [BLOCK: SIPP Indexer Service Endpoints]
# ======================================================================
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
        raise HTTPException(status_code=500, detail=f"Snapshot error: {exc}") from exc


# ======================================================================
# [BLOCK: ROUTER REGISTRATION]
# ======================================================================
app.include_router(verify_router)
if system_router is not None:
    app.include_router(system_router)
if export_router is not None:
    app.include_router(export_router)
if ledger_router is not None:
    app.include_router(ledger_router)


# ======================================================================
# [BLOCK: MAIN]
# ======================================================================
if __name__ == "__main__":
    uvicorn.run(
        "services.api_gateway.main:app", host="127.0.0.1", port=8000, reload=True
    )
