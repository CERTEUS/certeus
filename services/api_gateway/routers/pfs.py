#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/pfs.py                  |
# | ROLE: PFS (ProofFS) inspect API (read-only)                  |
# | PLIK: services/api_gateway/routers/pfs.py                  |
# | ROLA: API inspekcji PFS (ProofFS) w trybie tylko-do-odczytu  |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI — ProofFS (pfs://) inspektor: weryfikuje URI i zwraca
    podstawowe metadane (kind/hash) oraz szkic xattrs (PNIP/PCO) — read-only.

EN: FastAPI router — ProofFS (pfs://) inspector: validates URI and returns
    basic metadata (kind/hash) and a sketch of xattrs (PNIP/PCO) — read-only.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from dataclasses import dataclass
from urllib.parse import urlparse

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel, Field

from services.api_gateway.limits import enforce_limits

# === KONFIGURACJA / CONFIGURATION ===


@dataclass(slots=True)
class _PfsMeta:
    kind: str
    hash: str


def _classify_pfs(uri: str) -> _PfsMeta:
    u = urlparse(uri)
    if u.scheme != "pfs":
        raise ValueError("invalid scheme")
    path = (u.netloc + u.path).lstrip("/")
    # pfs://why-not/<hash>
    if path.startswith("why-not/") and len(path.split("/", 1)[1]) >= 8:
        h = path.split("/", 1)[1]
        return _PfsMeta(kind="why-not", hash=h)
    # pfs://mail/<id>
    if path.startswith("mail/"):
        ident = path.split("/", 1)[1]
        return _PfsMeta(kind="mail", hash=ident)
    # pfs://fin/<artifact>
    if path.startswith("fin/"):
        ident = path.split("/", 1)[1]
        return _PfsMeta(kind="fin", hash=ident)
    return _PfsMeta(kind="unknown", hash=path or "")


# === MODELE / MODELS ===


class InspectResponse(BaseModel):
    ok: bool = Field(True, description="Inspection succeeded")
    uri: str
    kind: str
    hash: str
    xattrs: dict[str, str] | None = None


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/pfs", tags=["pfs"])


@router.get("/inspect", response_model=InspectResponse, summary="Inspect pfs:// URI")
async def inspect(uri: str, request: Request) -> InspectResponse:
    enforce_limits(request, cost_units=1)
    try:
        meta = _classify_pfs(uri)
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"invalid pfs uri: {e}") from e
    # Minimal xattrs sketch (extend per-kind later)
    xattrs: dict[str, str] = {}
    if meta.kind == "why-not":
        xattrs = {"user.certeus.kind": "why-not"}
    elif meta.kind == "mail":
        xattrs = {"user.certeus.kind": "mail-attachment"}
    elif meta.kind == "fin":
        xattrs = {"user.certeus.kind": "fin-artifact"}
    return InspectResponse(ok=True, uri=uri, kind=meta.kind, hash=meta.hash, xattrs=xattrs)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
