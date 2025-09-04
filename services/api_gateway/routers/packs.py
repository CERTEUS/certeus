#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/packs.py               |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/packs.py               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla obszaru Domain Packs / capabilities.

EN: FastAPI router for Domain Packs / capabilities.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

from fastapi import APIRouter, HTTPException, Request
from pydantic import BaseModel

from packs_core.loader import discover, load as load_pack
from services.api_gateway.limits import enforce_limits

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class HandleRequest(BaseModel):
    pack: str

    kind: str

    payload: dict[str, Any] | None = None


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/packs", tags=["packs"])


def _repo_root() -> Path:
    from pathlib import Path as _P

    return _P(__file__).resolve().parents[3]


def _state_path() -> Path:
    p = os.getenv("PACKS_STATE_PATH")
    if p:
        return Path(p)
    return _repo_root() / "data" / "packs_state.json"


def _load_state() -> dict[str, bool]:
    try:
        sp = _state_path()
        if not sp.exists():  # no state yet
            return {}
        data = json.loads(sp.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            # normalize to bools
            return {str(k): bool(v) for k, v in data.items()}
    except Exception:
        return {}
    return {}


def _save_state(state: dict[str, bool]) -> None:
    sp = _state_path()
    sp.parent.mkdir(parents=True, exist_ok=True)
    sp.write_text(json.dumps(state, indent=2, sort_keys=True), encoding="utf-8")


@router.get("/", summary="List available packs")
async def list_packs() -> list[dict[str, Any]]:
    infos = discover()
    overrides = _load_state()
    return [
        {
            "name": i.name,
            "abi": i.abi,
            "capabilities": i.caps,
            "version": i.version,
            "enabled": bool(overrides.get(i.name, i.enabled)),
        }
        for i in infos
    ]


class ToggleRequest(BaseModel):
    pack: str
    enabled: bool


@router.post("/enable", summary="Enable or disable a pack")
async def enable_pack(req: ToggleRequest, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=1)

    # Optional: validate pack exists
    names = {i.name for i in discover()}
    if req.pack not in names:
        raise HTTPException(status_code=404, detail=f"unknown pack: {req.pack}")

    state = _load_state()
    state[req.pack] = bool(req.enabled)
    _save_state(state)
    return {"ok": True, "pack": req.pack, "enabled": bool(req.enabled)}


@router.get("/{name}", summary="Get pack details")
async def get_pack_details(name: str) -> dict[str, Any]:
    """
    Zwraca szczegóły pakietu na podstawie manifestu plugin.yaml oraz overlayu enabled.
    Returns pack details based on plugin.yaml manifest and enabled overlay.
    """
    # Find target info
    infos = {i.name: i for i in discover()}
    if name not in infos:
        raise HTTPException(status_code=404, detail=f"unknown pack: {name}")
    info = infos[name]
    # Try to locate manifest
    manifest: dict[str, Any] = {}
    try:
        plug_root = _repo_root() / "plugins" / name / "plugin.yaml"
        if plug_root.exists():
            import yaml  # type: ignore

            manifest = yaml.safe_load(plug_root.read_text(encoding="utf-8")) or {}
    except Exception:
        manifest = {}
    overrides = _load_state()
    return {
        "name": info.name,
        "version": info.version,
        "abi": info.abi,
        "capabilities": info.caps,
        "enabled": bool(overrides.get(info.name, info.enabled)),
        "manifest": manifest,
    }


@router.post("/handle", summary="Handle a request using a pack")
async def handle(req: HandleRequest, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=1)

    try:
        pack = load_pack(req.pack)

        result = pack.handle(req.kind, dict(req.payload or {}))

        return {"ok": True, "result": result}

    except Exception as e:  # nosec - błąd pakietu mapujemy na 400
        raise HTTPException(status_code=400, detail=f"pack handle error: {e}") from e


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
