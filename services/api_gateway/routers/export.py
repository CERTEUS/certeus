#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/api_gateway/routers/export.py  |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


"""
PL: Router /v1/export – waliduje ładunek i zapisuje raport w formacie TXT
    o konwencji nazwy `raport_{case_id}.txt`. Zwraca ścieżkę i komunikat.
EN: /v1/export router – validates payload and writes a TXT report named
    `raport_{case_id}.txt`. Returns file path and a message.
"""

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
from typing import Any, Mapping

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field

router = APIRouter(prefix="", tags=["export"])


class ExportPayload(BaseModel):
    case_id: str = Field(..., description="Public case id, e.g. 'pl-286kk-0001'")
    analysis_result: Mapping[str, Any] = Field(default_factory=dict)
    fmt: str = Field(
        "report", description="Output format. Only 'report' is used by tests."
    )


class ExportResponse(BaseModel):
    path: str
    message: str


def _write_report(
    case_id: str, analysis_result: Mapping[str, Any], out_dir: Path
) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    filename = f"raport_{case_id}.txt"
    path = out_dir / filename

    lines = []
    lines.append("# CERTEUS – Raport analityczny")
    lines.append(f"Case: {case_id}")
    lines.append(
        f"Digest: sha256:{sha256(repr(dict(analysis_result)).encode('utf-8')).hexdigest()}"
    )
    lines.append("")
    lines.append("=== ANALIZA ===")
    try:
        import json

        pretty = json.dumps(
            analysis_result, ensure_ascii=False, indent=2, sort_keys=True
        )
        lines.append(pretty)
    except Exception:
        lines.append(str(analysis_result))

    path.write_text("\n".join(lines), encoding="utf-8")
    return path


@router.post("/v1/export", response_model=ExportResponse)
def export_endpoint(payload: ExportPayload) -> ExportResponse:
    if not payload.case_id.strip():
        raise HTTPException(status_code=400, detail="case_id required")

    out_dir = Path("exports")
    path = _write_report(payload.case_id, payload.analysis_result, out_dir)

    return ExportResponse(
        path=str(path),
        message=f"Report generated at {path}",
    )
