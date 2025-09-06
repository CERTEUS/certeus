#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/pfs_dht.py             |
# | ROLE: ProofFS Competency-DHT (stub)                          |
# | PLIK: services/api_gateway/routers/pfs_dht.py             |
# | ROLA: DHT kompetencji (stub)                                 |
# +-------------------------------------------------------------+
"""
PL: Minimalny DHT kompetencji dla ProofFS: węzły ogłaszają kompetencje
    (wzorce), zapytania filtrują, publish_path sugeruje dystrybucję.

EN: Minimal competency DHT for ProofFS: nodes announce competencies
    (patterns), queries filter, publish_path suggests distribution.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import fnmatch
import json
import os
from pathlib import Path
from typing import Any

from fastapi import APIRouter, Request
from pydantic import BaseModel, Field

# === KONFIGURACJA / CONFIGURATION ===

_STORE = Path(__file__).resolve().parents[3] / "data" / "pfs_dht.json"
_MEM_DB: dict[str, dict[str, Any]] = {}

# === MODELE / MODELS ===


class AnnounceIn(BaseModel):
    node: str = Field(pattern=r"^[A-Za-z0-9_.:-]+$")
    competencies: list[str] = Field(min_length=1)
    capacity: int = Field(default=1, ge=0)
    ttl_sec: int | None = Field(default=None, ge=0)


class AnnounceOut(BaseModel):
    ok: bool
    count: int


class QueryOut(BaseModel):
    nodes: list[str]


class PublishPathIn(BaseModel):
    case: str
    path: list[str]


class PublishPathOut(BaseModel):
    assigned: dict[str, int]
    nodes: list[str]


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/pfs/dht", tags=["ProofFS-DHT"])


def _use_persistence() -> bool:
    return (os.getenv("PFS_DHT_PERSIST") or "").strip() in {"1", "true", "True"}


def _load() -> dict[str, dict[str, Any]]:
    if not _use_persistence():
        return _MEM_DB
    try:
        if _STORE.exists():
            raw = json.loads(_STORE.read_text(encoding="utf-8"))
            if isinstance(raw, dict):
                return raw
    except Exception:
        pass
    return {}


def _save(data: dict[str, dict[str, Any]]) -> None:
    if not _use_persistence():
        snapshot = dict(data)
        _MEM_DB.clear()
        _MEM_DB.update(snapshot)
        return
    try:
        _STORE.parent.mkdir(parents=True, exist_ok=True)
        _STORE.write_text(
            json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8"
        )
    except Exception:
        pass


@router.post("/announce", response_model=AnnounceOut)
async def announce(req: AnnounceIn, request: Request) -> AnnounceOut:
    _ = request  # rate-limit hook optional
    db = _load()
    db[req.node] = {
        "competencies": list(req.competencies),
        "capacity": int(req.capacity),
        "ttl_sec": int(req.ttl_sec) if req.ttl_sec is not None else None,
    }
    _save(db)
    return AnnounceOut(ok=True, count=len(db))


@router.get("/query", response_model=QueryOut)
async def query(competency: str) -> QueryOut:
    db = _load()
    nodes: list[str] = []
    for node, meta in db.items():
        comps = meta.get("competencies") if isinstance(meta, dict) else None
        if not isinstance(comps, list):
            continue
        # TTL filter: ttl_sec == 0 means expired; None -> no TTL check
        ttl = meta.get("ttl_sec") if isinstance(meta, dict) else None
        if isinstance(ttl, int) and ttl == 0:
            continue
        if any(
            fnmatch.fnmatch(competency, str(patt))
            or fnmatch.fnmatch(str(patt), competency)
            for patt in comps
        ):
            nodes.append(str(node))
    nodes.sort()
    return QueryOut(nodes=nodes)


@router.post("/publish_path", response_model=PublishPathOut)
async def publish_path(req: PublishPathIn) -> PublishPathOut:
    """PL/EN: Heurystycznie przypisz węzły do elementów ścieżki.

    Reguła: szukaj nodeów odpowiadających tokenom path (fnmatch), rozdzielaj
    równomiernie po pojawieniach; zwróć plan assigned {node: count}.
    """
    db = _load()
    nodes = sorted(db.keys())
    plan: dict[str, int] = {n: 0 for n in nodes}
    for token in req.path:
        best: list[str] = []
        for node, meta in db.items():
            comps = meta.get("competencies") if isinstance(meta, dict) else None
            if not isinstance(comps, list):
                continue
            if any(
                fnmatch.fnmatch(token, str(patt)) or fnmatch.fnmatch(str(patt), token)
                for patt in comps
            ):
                best.append(node)
        best.sort()
        if best:
            # wybierz najmniej obciążony z uwzględnieniem capacity: load/capacity
            def _load_factor(n: str) -> float:
                meta = db.get(n) or {}
                cap = int(meta.get("capacity", 1)) or 1
                return plan.get(n, 0) / float(max(1, cap))

            tgt = min(best, key=_load_factor)
            plan[tgt] = plan.get(tgt, 0) + 1
    # usuń zera
    plan = {k: v for k, v in plan.items() if v > 0}
    return PublishPathOut(assigned=plan, nodes=sorted(plan.keys()))


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
