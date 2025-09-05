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
PL: Router ProofFS (listowanie zasobów, exists). Listing dla prefiksu pfs:// + exists dla pojedynczego URI.

EN: ProofFS router (list and exists). Lists given pfs:// prefix and checks existence of a single URI.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

from fastapi import APIRouter, HTTPException, Query

# === KONFIGURACJA / CONFIGURATION ===

PFS_ROOT_ENV = "PROOFS_FS_ROOT"

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/pfs", tags=["ProofFS"])


def _root() -> Path:
    p = os.getenv(PFS_ROOT_ENV)
    if p:
        return Path(p)
    # fallback: repo data dir (aligned with materialize default)
    return Path(".").resolve() / "data" / "proof_fs"


@router.get("/list", operation_id="pfs_list_entries")
async def list_entries(
    prefix: str = Query(..., description="pfs:// prefix"),
    recursive: bool = Query(False, description="List recursively"),
    limit: int = Query(1000, ge=1, le=10000, description="Max entries to return"),
    mime: str | None = Query(None, description="Filter by simple mime/extension substring, e.g. 'pdf'"),
) -> dict[str, Any]:
    if not prefix.startswith("pfs://"):
        raise HTTPException(status_code=400, detail="prefix must start with pfs://")
    parts = prefix[len("pfs://") :].strip("/").split("/")
    path = _root().joinpath(*parts)
    if not path.exists() or not path.is_dir():
        raise HTTPException(status_code=404, detail="prefix not found")
    entries: list[dict[str, Any]] = []
    it = path.rglob("*") if recursive else path.iterdir()
    flt = (mime or "").lower().strip() if mime else None
    for p in sorted(it):
        if not p.is_file():
            continue
        if flt and flt not in p.name.lower():
            continue
        rel = p.relative_to(path).as_posix()
        entries.append({"uri": f"{prefix}/{rel}", "size": p.stat().st_size})
        if len(entries) >= limit:
            break
    return {"prefix": prefix, "entries": entries}


@router.get("/exists", operation_id="pfs_exists")
async def exists(uri: str = Query(..., description="pfs:// URI")) -> dict[str, Any]:
    if not uri.startswith("pfs://"):
        raise HTTPException(status_code=400, detail="uri must start with pfs://")
    parts = uri[len("pfs://") :].strip("/").split("/")
    p = _root().joinpath(*parts)
    if p.exists() and p.is_file():
        try:
            size = p.stat().st_size
        except Exception:
            size = None
        return {"uri": uri, "exists": True, "size": size, "path": str(p)}
    return {"uri": uri, "exists": False, "size": None, "path": str(p)}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
