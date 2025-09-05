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
PL: Router ProofFS: listowanie/exists oraz inspekcja ścieżek (z logu lexqft).

EN: ProofFS router: list/exists and inspection of paths (from lexqft log).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import base64
from hashlib import sha256
import json
import os
from pathlib import Path
from typing import Any

from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)
from fastapi import APIRouter, HTTPException, Query
from core.pfs.resolve import resolve_uri, resolve_prefix_dir
from core.pfs.materialize import materialize_uri
from core.pfs.xattrs import get_xattrs_for_uri
from core.pfs.mount import mount_readonly, unmount

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


def _tunnel_log_path() -> Path:
    return Path(__file__).resolve().parents[3] / "data" / "lexqft_tunnel_log.jsonl"


@router.get("/list", operation_id="pfs_list_entries")
async def list_entries(
    prefix: str = Query(..., description="pfs:// prefix"),
    recursive: bool = Query(False, description="List recursively"),
    limit: int = Query(1000, ge=1, le=10000, description="Max entries to return"),
    mime: str | None = Query(None, description="Filter by simple mime/extension substring, e.g. 'pdf'"),
) -> dict[str, Any]:
    if not prefix.startswith("pfs://"):
        raise HTTPException(status_code=400, detail="prefix must start with pfs://")
    # reuse core resolver to avoid drift
    try:
        path = resolve_prefix_dir(prefix, _root())
    except Exception as _e:
        raise HTTPException(status_code=400, detail=str(_e)) from _e
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


@router.get("/xattrs", operation_id="pfs_get_xattrs")
async def get_xattrs(uri: str = Query(..., description="pfs:// URI")) -> dict[str, Any]:
    if not isinstance(uri, str) or not uri.startswith("pfs://"):
        raise HTTPException(status_code=400, detail="uri must start with pfs://")
    try:
        x = get_xattrs_for_uri(uri)
    except FileNotFoundError:
        raise HTTPException(status_code=404, detail="artifact not found")
    except Exception as _e:
        raise HTTPException(status_code=400, detail=str(_e)) from _e
    return {"uri": uri, "xattrs": x}


@router.post("/materialize", operation_id="pfs_materialize")
async def materialize(body: dict[str, Any]) -> dict[str, Any]:
    """PL/EN: Materialize a stub artifact for given pfs:// URI (dev/test only)."""
    uri = str(body.get("uri") or "")
    if not uri.startswith("pfs://"):
        raise HTTPException(status_code=400, detail="uri must start with pfs://")
    try:
        p = materialize_uri(uri, meta=body.get("meta") or {})
    except Exception as _e:
        raise HTTPException(status_code=400, detail=str(_e)) from _e
    # Return exists/xattrs for convenience
    try:
        x = get_xattrs_for_uri(uri)
    except Exception:
        x = None
    return {"uri": uri, "path": str(p), "ok": True, "xattrs": x}


@router.post("/mount", operation_id="pfs_mount_mock")
async def mount(body: dict[str, Any] | None = None) -> dict[str, Any]:
    """PL/EN: Mock mount ProofFS (no‑op) for e2e flows and UI demos."""
    _ = body or {}
    src = (_ or {}).get("root")
    m = mount_readonly(src)
    return {"mounted": True, "mount_id": m.mount_id, "mount_path": str(m.mount_path)}


@router.post("/unmount", operation_id="pfs_unmount_mock")
async def unmount_(body: dict[str, Any]) -> dict[str, Any]:
    mid = str((body or {}).get("mount_id") or "")
    if not mid:
        raise HTTPException(status_code=400, detail="mount_id is required")
    ok = unmount(mid)
    if not ok:
        raise HTTPException(status_code=404, detail="mount not found")
    return {"unmounted": True, "mount_id": mid}


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


@router.get("/case/{case}")
async def case_paths(case: str) -> dict[str, Any]:
    """PL/EN: Return paths recorded by lexqft tunnel log for the given case."""
    log = _tunnel_log_path()
    paths: list[list[str]] = []
    try:
        if log.exists():
            for ln in log.read_text(encoding="utf-8").splitlines():
                s = ln.strip()
                if not s:
                    continue
                obj = json.loads(s)
                if str(obj.get("case_id")) == case and isinstance(obj.get("path"), list):
                    paths.append([str(x) for x in obj.get("path")])
    except Exception:
        paths = []
    return {"case": case, "paths": paths}


@router.get("/inspect")
async def inspect() -> dict[str, Any]:
    """PL/EN: List cases present in the lexqft tunnel log."""
    log = _tunnel_log_path()
    cases: set[str] = set()
    try:
        if log.exists():
            for ln in log.read_text(encoding="utf-8").splitlines():
                s = ln.strip()
                if not s:
                    continue
                obj = json.loads(s)
                cid = obj.get("case_id")
                if isinstance(cid, str) and cid:
                    cases.add(cid)
    except Exception:
        cases = set()
    return {"cases": sorted(cases)}


def _b64u_decode(s: str) -> bytes:
    pad = "=" * (-len(s) % 4)
    return base64.urlsafe_b64decode(s + pad)


def _b64u_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).decode("ascii").rstrip("=")


def _merkle_root(path: list[str]) -> bytes:
    if not path:
        return sha256(b"").digest()
    level = [sha256(str(x).encode("utf-8")).digest() for x in path]
    while len(level) > 1:
        nxt: list[bytes] = []
        it = iter(level)
        for a in it:
            try:
                b = next(it)
            except StopIteration:
                b = a
            nxt.append(sha256(a + b).digest())
        level = nxt
    return level[0]


@router.post("/sign_path")
async def sign_path(body: dict) -> dict[str, Any]:
    case = str(body.get("case") or "")
    path = body.get("path") or []
    sk_b64 = str(body.get("sk_b64url") or "")
    if not isinstance(path, list) or not sk_b64:
        raise HTTPException(status_code=400, detail="invalid payload")
    root = _merkle_root([str(x) for x in path])
    sk_raw = _b64u_decode(sk_b64)
    try:
        sk = Ed25519PrivateKey.from_private_bytes(sk_raw)
    except Exception as _e:
        raise HTTPException(status_code=400, detail="invalid secret key") from _e
    sig = sk.sign(root)
    return {"case": case, "signature_b64": _b64u_encode(sig)}


@router.post("/verify_path")
async def verify_path(body: dict) -> dict[str, Any]:
    case = str(body.get("case") or "")
    path = body.get("path") or []
    pk_b64 = str(body.get("pk_b64url") or "")
    sig_b64 = str(body.get("signature_b64") or "")
    if not isinstance(path, list) or not pk_b64 or not sig_b64:
        raise HTTPException(status_code=400, detail="invalid payload")
    root = _merkle_root([str(x) for x in path])
    pk_raw = _b64u_decode(pk_b64)
    sig = _b64u_decode(sig_b64)
    try:
        pk = Ed25519PublicKey.from_public_bytes(pk_raw)
        pk.verify(sig, root)
        ok = True
    except Exception:
        ok = False
    return {"case": case, "ok": bool(ok)}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
