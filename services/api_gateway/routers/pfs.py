#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/pfs.py                 |
# | ROLE: Read-only ProofFS inspection API                      |
# | PLIK: services/api_gateway/routers/pfs.py                 |
# | ROLA: Read-only API inspekcji ProofFS                       |
# +-------------------------------------------------------------+
"""
PL: Read-only inspekcja ProofFS: ścieżki dowodowe per-case.
EN: Read-only ProofFS inspection: proof paths per case.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path

from fastapi import APIRouter
from pydantic import BaseModel

# === KONFIGURACJA / CONFIGURATION ===

_STORE = Path(__file__).resolve().parents[3] / "data" / "pfs_paths.json"

# === MODELE / MODELS ===


class PFSCaseResponse(BaseModel):
    case: str
    paths: list[list[str]]


class PFSInspectResponse(BaseModel):
    cases: list[str]
    counts: dict[str, int]


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/pfs", tags=["ProofFS"])


def _load() -> dict[str, list[dict]]:
    try:
        if _STORE.exists():
            data = json.loads(_STORE.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                # normalize: ensure list[dict]
                out: dict[str, list[dict]] = {}
                for k, v in data.items():
                    if isinstance(v, list):
                        out[k] = [x for x in v if isinstance(x, dict)]
                return out
    except Exception:
        pass
    return {}


@router.get("/inspect", response_model=PFSInspectResponse)
async def inspect() -> PFSInspectResponse:
    data = _load()
    cases = sorted(data.keys())
    counts = {k: len(v) for k, v in data.items()}
    return PFSInspectResponse(cases=cases, counts=counts)


@router.get("/case/{case_id}", response_model=PFSCaseResponse)
async def case(case_id: str) -> PFSCaseResponse:
    data = _load()
    recs = data.get(case_id) or []
    paths = [list(x.get("path")) for x in recs if isinstance(x.get("path"), list)]
    return PFSCaseResponse(case=case_id, paths=paths)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
