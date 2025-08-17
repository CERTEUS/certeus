#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE / MODUŁ: services/api_gateway/routers/export.py              |
# | DATE / DATA: 2025-08-17                                             |
# +=====================================================================+
# | ROLE / ROLA:                                                        |
# |  EN: /v1/export – validate payload and write a TXT report           |
# |      named `raport_{case_id}.txt`. Enrich response with provenance  |
# |      (sha256, timestamp_utc, artifacts).                            |
# |  PL: /v1/export – walidacja ładunku i zapis raportu TXT             |
# |      `raport_{case_id}.txt`. Odpowiedź wzbogacona o provenance      |
# |      (sha256, timestamp_utc, artifacts).                            |
# +=====================================================================+

"""
PL: Endpoint eksportu. Przyjmuje `case_id` i `analysis_result`, zapisuje raport
    tekstowy do katalogu `exports/`, po czym zwraca ścieżkę oraz provenance
    zawierające hash SHA-256 pliku raportu, znacznik czasu UTC i listę artefaktów.
EN: Export endpoint. Accepts `case_id` and `analysis_result`, writes a text
    report under `exports/`, then returns the path and provenance with the
    report file's SHA-256, UTC timestamp, and artifacts list.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Optional

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field

import hashlib
import json
from datetime import datetime, timezone

router = APIRouter(prefix="", tags=["export"])


# === MODELS / MODELE ===
class ExportPayload(BaseModel):
    case_id: str = Field(..., description="Public case id, e.g. 'pl-286kk-0001'")
    analysis_result: Mapping[str, Any] = Field(default_factory=dict)
    fmt: str = Field("report", description="Output format (tests use 'report').")


class ExportResponse(BaseModel):
    path: str
    message: str
    provenance: Optional[dict[str, Any]] = None  # optional to keep tests happy


# === HELPERS ===
def _hash_file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _now_iso_utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def _write_report(
    case_id: str, analysis_result: Mapping[str, Any], out_dir: Path
) -> Path:
    """
    PL: Zapis raportu jako .txt z podstawowym podsumowaniem i pretty JSON.
    EN: Write .txt report with a tiny header + pretty JSON of the analysis.
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    filename = f"raport_{case_id}.txt"
    path = out_dir / filename

    lines: list[str] = []
    lines.append("# CERTEUS – Raport analityczny / Analytical Report")
    lines.append(f"Case: {case_id}")
    try:
        pretty = json.dumps(
            analysis_result, ensure_ascii=False, indent=2, sort_keys=True
        )
    except Exception:
        pretty = str(analysis_result)
    lines.append("")
    lines.append("=== ANALIZA / ANALYSIS ===")
    lines.append(pretty)

    path.write_text("\n".join(lines), encoding="utf-8")
    return path


# === ENDPOINT ===
@router.post("/v1/export", response_model=ExportResponse)
def export_endpoint(payload: ExportPayload) -> ExportResponse:
    """
    PL: Generuje raport i zwraca ścieżkę + provenance (hash, timestamp, artifacts).
    EN: Generate report and return path + provenance (hash, timestamp, artifacts).
    """
    case_id = payload.case_id.strip()
    if not case_id:
        raise HTTPException(status_code=400, detail="case_id required")

    out_dir = Path("exports")
    path = _write_report(case_id, payload.analysis_result, out_dir)

    # Build provenance / Budowa provenance
    prov: dict[str, Any] = {
        "hash_sha256": _hash_file_sha256(path),
        "timestamp_utc": _now_iso_utc(),
        "artifacts": {
            "report": str(path),
        },
    }

    return ExportResponse(
        path=str(path),
        message=f"Report generated at {path}",
        provenance=prov,
    )
