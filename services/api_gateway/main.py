# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/main.py                          |
# | ROLE: FastAPI application wiring public routers & /health.  |
# | PLIK: services/api_gateway/main.py                          |
# | ROLA: Aplikacja FastAPI spinająca routery publiczne i /health|
# +-------------------------------------------------------------+
"""
PL: Główna aplikacja API. Dołącza routery (w tym /v1/verify) oraz /health.
EN: Main API app. Attaches routers (including /v1/verify) and /health.
"""

# === IMPORTY / IMPORTS ======================================== #
from __future__ import annotations
from fastapi import FastAPI

from fastapi import UploadFile, File, HTTPException
from typing import List
import asyncio

from services.ingest_service.ocr_pipeline import OcrPipeline
from services.ingest_service.factlog_mapper import FactlogMapper
from services.ingest_service.models import Fact

# [ROUTER IMPORTS – BEZPOŚREDNIO Z MODUŁÓW]
# Wymagany przez Dzień 5: /v1/verify
from services.api_gateway.routers.verify import router as verify_router

# Opcjonalne – jeśli masz te moduły w repo, podepniemy ich routery;
# jeśli nie, continue gracefully.
try:
    from services.api_gateway.routers.system import router as system_router  # type: ignore
except Exception:  # pragma: no cover
    system_router = None  # type: ignore

try:
    from services.api_gateway.routers.export import router as export_router  # type: ignore
except Exception:  # pragma: no cover
    export_router = None  # type: ignore

try:
    from services.api_gateway.routers.ledger import router as ledger_router  # type: ignore
except Exception:  # pragma: no cover
    ledger_router = None  # type: ignore


# === APLIKACJA / APP ========================================== #
app = FastAPI(title="CERTEUS API", version="1.0")


# === REJESTRACJA ROUTERÓW / ROUTER REGISTRATION =============== #
# Kluczowe: verify – dodaje ścieżkę /v1/verify do OpenAPI
app.include_router(verify_router)

# Opcjonalne (jeśli moduły istnieją u Ciebie w repo):
if system_router is not None:
    app.include_router(system_router)
if export_router is not None:
    app.include_router(export_router)
if ledger_router is not None:
    app.include_router(ledger_router)


# === HEALTHCHECK ============================================== #
@app.get("/health")
def health() -> dict[str, bool]:
    """
    PL: Prosty endpoint sprawdzający żywotność API.
    EN: Simple endpoint to check API liveness.
    """
    return {"ok": True}


# [BLOCK: INGEST INIT]
ocr_pipeline = OcrPipeline()
factlog_mapper = FactlogMapper()

ALLOWED_MIME = {"application/pdf", "text/plain", "image/png", "image/jpeg"}
MAX_BYTES = 10 * 1024 * 1024  # 10 MB


# [BLOCK: /v1/ingest ENDPOINT]
@app.post("/v1/ingest", response_model=List[Fact], tags=["Ingestion Service"])
async def ingest_document(file: UploadFile = File(...)):
    """
    PL: Przyjmuje dokument, uruchamia stub OCR i mapowanie do FACTLOG, zwraca listę faktów.
        Bezpieczeństwo: weryfikacja MIME, limit rozmiaru, timeout.

    EN: Accepts a document, runs OCR stub and FACTLOG mapping, returns a list of facts.
        Safety: MIME validation, size limit, timeout.
    """
    if file.content_type not in ALLOWED_MIME:
        raise HTTPException(status_code=415, detail="Unsupported media type")

    data = await file.read()
    if len(data) > MAX_BYTES:
        raise HTTPException(status_code=413, detail="File too large")

    try:
        # uruchom stub OCR w wątku + timeout, żeby nie blokować event loop
        ocr_output = await asyncio.wait_for(
            asyncio.to_thread(ocr_pipeline.process_document, data), timeout=15
        )
    except asyncio.TimeoutError:
        raise HTTPException(status_code=504, detail="OCR timeout")

    facts = factlog_mapper.map_to_facts(ocr_output, data)
    return facts
