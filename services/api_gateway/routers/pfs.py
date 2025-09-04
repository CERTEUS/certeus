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
PL: Router ProofFS (listowanie zasobów). Prosty listing dla prefiksu pfs://.

EN: ProofFS router (resource listing). Simple listing for pfs:// prefix.
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
    # fallback: repo data dir
    return Path(".").resolve() / "data" / "pfs"


@router.get("/list")
async def list_entries(prefix: str = Query(..., description="pfs:// prefix")) -> dict[str, Any]:
    if not prefix.startswith("pfs://"):
        raise HTTPException(status_code=400, detail="prefix must start with pfs://")
    parts = prefix[len("pfs://") :].strip("/").split("/")
    path = _root().joinpath(*parts)
    if not path.exists() or not path.is_dir():
        raise HTTPException(status_code=404, detail="prefix not found")
    entries: list[dict[str, Any]] = []
    for p in sorted(path.iterdir()):
        if p.is_file():
            entries.append({"uri": f"{prefix}/{p.name}", "size": p.stat().st_size})
    return {"prefix": prefix, "entries": entries}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
