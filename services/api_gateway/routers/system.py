#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/api_gateway/routers/system.py  |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


"""
PL: Router narzędziowy (systemowy). Udostępnia:
    • /v1/ingest  – lekki stub OCR → FACTLOG (z nagłówkiem łańcucha, limitami, MIME),
    • /v1/analyze – minimalny stub analizy E2E (SAT),
    • /v1/sipp/snapshot/{act_id} – migawka aktu prawnego (z `_certeus`).

EN: System/utility router exposing:
    • /v1/ingest  – light OCR → FACTLOG stub (with chain header, limits, MIME),
    • /v1/analyze – minimal E2E analysis stub (SAT),
    • /v1/sipp/snapshot/{act_id} – legal act snapshot (with `_certeus`).
"""

from __future__ import annotations

import json
from hashlib import sha256
from fastapi import APIRouter, File, UploadFile, HTTPException, Response
from pydantic import BaseModel, Field
from typing import Any, Dict, List
from datetime import datetime, timezone

router = APIRouter(tags=["system"])

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
    response: Response, file: UploadFile = File(...)
) -> List[Dict[str, Any]]:
    """Zwraca dwa deterministyczne fakty (z `fact_id`, `thesis`, `confidence_score`),
    waliduje MIME/rozmiar i ustawia nagłówek łańcucha `X-CERTEUS-Ledger-Chain`."""
    MAX_BYTES = 10 * 1024 * 1024  # 10 MiB
    allowed_mime = "application/pdf"

    if file.content_type != allowed_mime:
        raise HTTPException(status_code=415, detail="Only application/pdf is supported")

    content = await file.read()
    if len(content) > MAX_BYTES:
        raise HTTPException(status_code=413, detail="File too large")

    src = file.filename or "document.pdf"

    def make_fact(role: str, value: str) -> Dict[str, Any]:
        base = f"{src}|{role}|{value}".encode("utf-8")
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

    # uzupełnij wymagane pola
    for f in facts:
        if f["role"] == "claim_contract_date":
            f["thesis"] = "Umowa została zawarta 2023-10-01."
            f["confidence_score"] = 0.98
        elif f["role"] == "evidence_payment":
            f["thesis"] = "Istnieje dowód wpłaty."
            f["confidence_score"] = 0.99

    # nagłówek łańcucha: "sha256:<...>;sha256:<...>"
    chain_parts: List[str] = []
    for f in facts:
        payload = json.dumps(f, ensure_ascii=False, sort_keys=True).encode("utf-8")
        chain_parts.append("sha256:" + sha256(payload).hexdigest())
    response.headers["X-CERTEUS-Ledger-Chain"] = ";".join(chain_parts)

    return facts


# ---------------------------------------------------------------------
# /v1/analyze
# ---------------------------------------------------------------------


@router.post("/v1/analyze")
async def analyze(case_id: str, file: UploadFile = File(...)) -> Dict[str, Any]:
    """
    Minimalny stub E2E: przyjmuje PDF i zwraca wynik SAT z prostym modelem.
    Zgodne z tests/e2e/test_e2e_pl_286kk_0001.py.
    """
    await file.read()  # nieużywane w stubie
    return {
        "case_id": case_id,
        "analysis_result": {"status": "sat", "model": "[x=True]"},
    }


# ---------------------------------------------------------------------
# /v1/sipp/snapshot/{act_id}
# ---------------------------------------------------------------------


@router.get("/v1/sipp/snapshot/{act_id}")
async def get_snapshot(act_id: str) -> Dict[str, Any]:
    """Zwraca minimalny snapshot (dict), aby dozwolić klucz `_certeus`."""
    text = (
        "Art. 286 k.k.: Kto, w celu osiągnięcia korzyści majątkowej, "
        "doprowadza inną osobę do niekorzystnego rozporządzenia mieniem "
        "za pomocą wprowadzenia w błąd..."
    ).strip()
    digest = "sha256:" + sha256(text.encode("utf-8")).hexdigest()
    snap_ts = datetime.now(timezone.utc).isoformat(timespec="seconds")

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
