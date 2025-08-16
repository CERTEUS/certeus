# +-------------------------------------------------------------+
# |                CERTEUS - API Gateway (E2E)                  |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/app_e2e.py                       |
# | ROLE: Orchestration endpoints for Day 9/10 MVP.             |
# +-------------------------------------------------------------+
"""
PL: Minimalny API Gateway na D9/D10: /v1/analyze (E2E) i /v1/export (raport).
EN: Minimal API Gateway for D9/D10: /v1/analyze (E2E) and /v1/export (report).
"""

from __future__ import annotations
from fastapi import FastAPI, UploadFile, File, HTTPException
from pydantic import BaseModel
from typing import Any, Dict, List
from pathlib import Path

from services.lexlog_parser.parser import LexlogParser
from kernel.e2e_verifier import DualCoreVerifier
from kernel.smt_translator import SimpleFact
from services.exporter_service.exporter import ExporterService

app = FastAPI(title="CERTEUS E2E API (Day 9/10 MVP)")

lexlog_parser = LexlogParser()
verifier = DualCoreVerifier()
exporter_service = ExporterService()


# ---- Stub ingest (Day 9) -------------------------------------
def _stub_ingest(document_bytes: bytes) -> List[SimpleFact]:
    return [
        SimpleFact(role="intent_financial_gain", value=True),
        SimpleFact(role="act_deception", value=True),
        SimpleFact(role="detrimental_property_disposal", value=True),
    ]


# ---- Orchestration: /v1/analyze -------------------------------
@app.post("/v1/analyze", tags=["Orchestration"])
async def analyze(case_id: str, file: UploadFile = File(...)) -> Dict[str, Any]:
    try:
        doc = await file.read()
        facts = _stub_ingest(doc)

        rules_path = Path("packs/jurisdictions/PL/rules/kk.lex")
        rules_content = rules_path.read_text(encoding="utf-8")

        parsed = lexlog_parser.parse(rules_content)
        result = verifier.analyze_case(facts, parsed)
        return {"case_id": case_id, "analysis_result": result}
    except Exception as e:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Analyze error: {e}")


# ---- Exporter: /v1/export ------------------------------------
class ExportRequest(BaseModel):
    case_id: str
    analysis_result: Dict[str, Any]


@app.post("/v1/export", tags=["Exporter Service"])
def export_analysis_report(request: ExportRequest) -> Dict[str, Any]:
    try:
        out_path = exporter_service.export_report(
            request.case_id, request.analysis_result
        )
        return {"message": "Report generated successfully", "path": str(out_path)}
    except Exception as e:  # pragma: no cover
        raise HTTPException(status_code=500, detail=f"Export error: {e}")
