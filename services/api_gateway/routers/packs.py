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

import inspect
import json
import os
from pathlib import Path
import re
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


def _load_state() -> dict[str, dict[str, Any]]:
    try:
        sp = _state_path()
        if not sp.exists():  # no state yet
            return {}
        data = json.loads(sp.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            norm: dict[str, dict[str, Any]] = {}
            for k, v in data.items():
                if isinstance(v, bool):
                    norm[str(k)] = {"enabled": bool(v)}
                elif isinstance(v, dict):
                    dv = dict(v)
                    dv["enabled"] = bool(dv.get("enabled", False))
                    norm[str(k)] = dv
            return norm
    except Exception:
        return {}
    return {}


def _save_state(state: dict[str, dict[str, Any]]) -> None:
    sp = _state_path()
    sp.parent.mkdir(parents=True, exist_ok=True)
    sp.write_text(json.dumps(state, indent=2, sort_keys=True), encoding="utf-8")


@router.get("/", summary="List available packs")
@router.get("", summary="List available packs (alias)")
async def list_packs() -> list[dict[str, Any]]:
    infos = discover()
    overrides = _load_state()
    return [
        {
            "name": i.name,
            "abi": i.abi,
            "capabilities": i.caps,
            "version": i.version,
            "enabled": bool(overrides.get(i.name, {}).get("enabled", i.enabled)),
            "signature": bool(overrides.get(i.name, {}).get("signature")),
            "installed_version": overrides.get(i.name, {}).get("installed_version"),
        }
        for i in infos
    ]


class ToggleRequest(BaseModel):
    pack: str
    enabled: bool


class InstallRequest(BaseModel):
    pack: str
    signature: str
    version: str | None = None


@router.post("/install", summary="Install or upgrade a pack (signature required)")
async def install_pack(req: InstallRequest, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=1)

    # Validate pack exists
    names = {i.name for i in discover()}
    if req.pack not in names:
        raise HTTPException(status_code=404, detail=f"unknown pack: {req.pack}")

    import re as _re

    sig = (req.signature or "").strip()
    # Require at least 64 hex chars (report-only semantics preserved for tests using 'a'*64/'A'*64)
    if not _re.fullmatch(r"[0-9a-fA-F]{64,}", sig):
        raise HTTPException(status_code=400, detail="invalid signature: expected hex(64+) string")

    # Persist signature and installed_version in state
    state = _load_state()
    cur = state.get(req.pack, {"enabled": True})
    cur["signature"] = sig
    if req.version:
        cur["installed_version"] = str(req.version)
    state[req.pack] = cur
    _save_state(state)

    return {"ok": True, "pack": req.pack, "signature": True, "installed_version": cur.get("installed_version")}


@router.post("/enable", summary="Enable or disable a pack")
async def enable_pack(req: ToggleRequest, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=1)

    # Optional: validate pack exists
    names = {i.name for i in discover()}
    if req.pack not in names:
        raise HTTPException(status_code=404, detail=f"unknown pack: {req.pack}")

    state = _load_state()
    cur = state.get(req.pack, {"enabled": False})
    cur["enabled"] = bool(req.enabled)
    state[req.pack] = cur
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
    # Simple SemVer + baseline status
    ver = info.version or ""
    semver_ok = bool(re.match(r"^\d+\.\d+\.\d+$", ver))
    baseline_present = (_repo_root() / "plugins" / name / "abi_baseline.json").exists()
    return {
        "name": info.name,
        "version": info.version,
        "abi": info.abi,
        "capabilities": info.caps,
        "enabled": bool(overrides.get(info.name, {}).get("enabled", info.enabled)),
        "manifest": manifest,
        "status": {"semver_ok": semver_ok, "baseline_present": baseline_present},
        "installed_version": overrides.get(info.name, {}).get("installed_version"),
        "signature_present": bool(overrides.get(info.name, {}).get("signature")),
    }


@router.get("/{name}/baseline", summary="Get ABI baseline JSON if present")
async def get_pack_baseline(name: str) -> dict[str, Any]:
    infos = {i.name: i for i in discover()}
    if name not in infos:
        raise HTTPException(status_code=404, detail=f"unknown pack: {name}")
    p = _repo_root() / "plugins" / name / "abi_baseline.json"
    if not p.exists():
        raise HTTPException(status_code=404, detail="baseline not found")
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"cannot read baseline: {e}") from e


class TryRequest(BaseModel):
    pack: str
    kind: str | None = None
    payload: dict[str, Any] | None = None


class _MiniAPI:
    def __init__(self) -> None:
        self.plugins: dict[str, Any] = {}
        self.adapters: dict[str, Any] = {}
        self.exporters: dict[str, Any] = {}

    def register_plugin(self, name: str, meta: Any) -> None:  # compat for plugin.register(api)
        self.plugins[name] = meta

    def register_adapter(self, key: str, fn: Any) -> None:
        self.adapters[key] = fn

    def register_exporter(self, key: str, fn: Any) -> None:
        self.exporters[key] = fn


def _module_path_for(name: str) -> str | None:
    p = _repo_root() / "plugins" / name / "plugin.yaml"
    if not p.exists():
        return None
    try:
        import yaml  # type: ignore

        data = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
        mod = str(data.get("module") or "").strip()
        return mod or None
    except Exception:
        return None


@router.post("/try", summary="Try invoking a pack (best-effort)")
async def try_pack(req: TryRequest, request: Request) -> dict[str, Any]:
    enforce_limits(request, cost_units=1)
    names = {i.name for i in discover()}
    if req.pack not in names:
        raise HTTPException(status_code=404, detail=f"unknown pack: {req.pack}")

    mod_path = _module_path_for(req.pack)
    if not mod_path:
        return {"ok": False, "reason": "no module path in manifest"}
    try:
        mod = __import__(mod_path, fromlist=["*"])  # nosec - local manifest
    except Exception as e:
        return {"ok": False, "reason": f"import error: {e}"}
    api = _MiniAPI()
    reg = getattr(mod, "register", None)
    if not callable(reg):
        return {"ok": False, "reason": "module has no register(api)"}
    try:
        reg(api)  # type: ignore[misc]
    except Exception as e:
        return {"ok": False, "reason": f"register() error: {e}"}

    # Prefer exporters (format JSON)
    if api.exporters:
        key, fn = next(iter(api.exporters.items()))
        sample = req.payload or {"case_id": "DEMO", "status": "ok", "model": "demo"}
        try:
            kwargs: dict[str, Any] = {}
            if "fmt" in inspect.signature(fn).parameters:
                kwargs["fmt"] = "json"
            res = fn(sample, **kwargs)  # type: ignore[misc]
            return {"ok": True, "used": {"type": "exporter", "key": key}, "result": res}
        except Exception as e:  # pragma: no cover
            return {"ok": False, "used": {"type": "exporter", "key": key}, "reason": str(e)}

    # Fallback: adapters
    if api.adapters:
        key, fn = next(iter(api.adapters.items()))
        sig = inspect.signature(fn)
        args: list[Any] = []
        for pname, param in sig.parameters.items():
            if param.kind in (param.VAR_POSITIONAL, param.VAR_KEYWORD):
                continue
            n = pname.lower()
            if n in {"case", "case_id", "act_id"}:
                args.append("DEMO-CASE")
            elif n in {"v_from", "from_version", "v1"}:
                args.append("v1")
            elif n in {"v_to", "to_version", "v2"}:
                args.append("v2")
            elif n in {"out_dir", "output_dir", "out", "dest"}:
                # avoid writing to fs in try
                continue
            else:
                args.append("demo")
        try:
            res = fn(*args)  # type: ignore[misc]
            return {"ok": True, "used": {"type": "adapter", "key": key}, "result": res}
        except Exception as e:  # pragma: no cover
            return {"ok": False, "used": {"type": "adapter", "key": key}, "reason": str(e)}

    return {"ok": False, "reason": "no exporters/adapters registered"}


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
