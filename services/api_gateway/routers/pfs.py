#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/pfs.py                 |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/pfs.py                 |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Router ProofFS – proste rozwiązywanie URI pfs:// do ścieżek i metadanych.
EN: ProofFS router – simple pfs:// URI resolver returning path and metadata.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from typing import Any

from fastapi import APIRouter, HTTPException, Query

from core.pfs.resolve import resolve_uri

# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/pfs", tags=["ProofFS"])


@router.get("/resolve")
def resolve(uri: str = Query(..., description="ProofFS URI, e.g. pfs://mail/MID/file.pdf")) -> dict[str, Any]:
    try:
        res = resolve_uri(uri)
    except ValueError as e:
        # clarify user errors cleanly; no internal chaining
        raise HTTPException(status_code=400, detail=str(e)) from None
    payload: dict[str, Any] = {
        "ok": True,
        "uri": res.uri,
        "exists": res.exists,
        "path": str(res.path),
    }
    if res.exists:
        payload["size"] = res.size
    return payload


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
