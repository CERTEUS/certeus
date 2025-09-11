#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/marketplace.py          |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/marketplace.py          |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Router FastAPI – Marketplace wtyczek (lista, weryfikacja, instalacja).

EN: FastAPI router – Plugin Marketplace (list, verify, install).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import yaml
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field

from core.plugin_loader import \
    _discover_plugins as discover_plugins  # type: ignore[attr-defined]
from packs_core.loader import PackInfo
from packs_core.loader import discover as discover_packs
from security.key_manager import load_ed25519_public_bytes

# === KONFIGURACJA / CONFIGURATION ===

_REPO_ROOT = Path(__file__).resolve().parents[3]
_PLUGINS_DIR = _REPO_ROOT / "plugins"


# === MODELE / MODELS ===


@dataclass(slots=True)
class PluginEntry:
    name: str
    module: str | None
    version: str | None
    signed: bool
    caps: list[str]


class VerifyRequest(BaseModel):
    manifest_yaml: str = Field(..., description="Plugin manifest (YAML)")
    signature_b64u: str = Field(..., min_length=40, description="Detached signature")


class InstallRequest(BaseModel):
    name: str
    manifest_yaml: str
    signature_b64u: str


# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/marketplace", tags=["marketplace"])


def _verify_manifest(manifest_yaml: str, signature_b64u: str) -> bool:
    """PL: Sprawdza podpis Ed25519 manifestu YAML (base64url, bez '=').

    EN: Verifies Ed25519 signature of YAML manifest (base64url, no '=').

    Zwraca True/False. Klucz publiczny pobierany przez `security.key_manager`.
    """
    try:
        pub = Ed25519PublicKey.from_public_bytes(load_ed25519_public_bytes())
        # Normalize b64url input padding
        sig = signature_b64u.encode("ascii")
        pad = b"=" * (-len(sig) % 4)
        import base64

        sig_bytes = base64.urlsafe_b64decode(sig + pad)
        pub.verify(sig_bytes, manifest_yaml.encode("utf-8"))
        return True
    except Exception:
        return False


@router.get("/pubkey", summary="Return current Ed25519 public key (b64url)")
def get_pubkey() -> dict[str, str] | dict[str, bool]:
    """PL: Zwraca publiczny klucz Ed25519 w base64url; 404 gdy brak.

    EN: Returns Ed25519 public key as base64url; 404-like response if missing.
    """

    try:
        b = load_ed25519_public_bytes()
        import base64

        return {"ed25519_pubkey_b64url": base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")}
    except Exception:
        return {"ok": False}


@router.get("/plugins", summary="List installed plugins")
def list_plugins() -> list[dict[str, Any]]:
    """PL: Wypisuje zainstalowane wtyczki i ich metadane (moduł, wersja, caps, signed).

    EN: Lists installed plugins with metadata (module, version, caps, signed).
    """
    # Core plugin loader specs (from plugin.yaml)
    specs = discover_plugins()  # type: ignore[call-arg]
    spec_map: dict[str, Any] = {s.name: s for s in specs}
    # Packs discovery (caps)
    packs: list[PackInfo] = discover_packs()
    caps_map: dict[str, list[str]] = {p.name: list(p.caps) for p in packs}

    out: list[PluginEntry] = []
    for name, spec in spec_map.items():
        man_path = _PLUGINS_DIR / name / "plugin.yaml"
        man_text = man_path.read_text(encoding="utf-8") if man_path.exists() else ""
        # Signed if manifest carries a 'signature' field that verifies
        signed = False
        try:
            data = yaml.safe_load(man_text) or {}
            signature = data.get("signature")
            if isinstance(signature, str) and signature:
                signed = _verify_manifest(man_text.replace(f"signature: {signature}", "signature:"), signature)
        except Exception:
            signed = False
        out.append(
            PluginEntry(
                name=name,
                module=(str(getattr(spec, "module", None)) if getattr(spec, "module", None) else None),
                version=getattr(spec, "version", None),
                signed=signed,
                caps=caps_map.get(name, []),
            )
        )
    return [asdict(x) for x in out]


@router.post("/verify_manifest", summary="Verify signed manifest")
def verify_manifest(req: VerifyRequest) -> dict[str, Any]:
    """PL: Weryfikacja podpisu Ed25519 manifestu YAML.

    EN: Verify Ed25519 signature of YAML manifest.
    """
    ok = _verify_manifest(req.manifest_yaml, req.signature_b64u)
    return {"ok": bool(ok)}


@router.post("/install", summary="Install/upgrade plugin (signed)")
def install_plugin(req: InstallRequest) -> dict[str, Any]:
    """PL: Instalacja/aktualizacja wtyczki po zweryfikowanym podpisie.

    EN: Install/upgrade plugin after verified signature.
    """
    # Name & path hardening first
    if not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", req.name):
        raise HTTPException(status_code=400, detail="Invalid plugin name")
    pdir = (_PLUGINS_DIR / req.name).resolve()
    plugins_root = _PLUGINS_DIR.resolve()
    if not str(pdir).startswith(str(plugins_root)):
        raise HTTPException(status_code=400, detail="Invalid destination path")
    # Then signature verification
    if not _verify_manifest(req.manifest_yaml, req.signature_b64u):
        raise HTTPException(status_code=400, detail="Invalid signature")
    # Basic YAML sanity
    try:
        data = yaml.safe_load(req.manifest_yaml) or {}
        mod = str(data.get("module") or "").strip()
        if not mod:
            raise ValueError("Manifest missing 'module'")
    except Exception as e:  # nosec - user-provided YAML validation
        raise HTTPException(status_code=400, detail=f"Invalid manifest: {e}") from e

    # pdir resolved above
    pdir.mkdir(parents=True, exist_ok=True)
    (pdir / "plugin.yaml").write_text(req.manifest_yaml, encoding="utf-8")
    return {"ok": True, "name": req.name, "path": str(pdir)}


@router.post("/sign_manifest", summary="Sign manifest (dev-only)")
def sign_manifest(payload: dict[str, Any]) -> dict[str, Any]:
    """PL: Podpisuje YAML Ed25519 (tylko DEV). Włącz przez MARKETPLACE_SIGNING_ENABLED=1.

    EN: Signs YAML with Ed25519 (DEV only). Enable via MARKETPLACE_SIGNING_ENABLED=1.
    """
    if (os.getenv("MARKETPLACE_SIGNING_ENABLED") or "").strip() not in {
        "1",
        "true",
        "True",
    }:
        raise HTTPException(status_code=403, detail="Signing disabled")
    import base64

    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import \
        Ed25519PrivateKey

    from security.key_manager import load_ed25519_private_pem

    text = str(payload.get("manifest_yaml") or "")
    if not text.strip():
        raise HTTPException(status_code=400, detail="manifest_yaml required")
    pem = load_ed25519_private_pem()
    sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
    assert isinstance(sk, Ed25519PrivateKey)
    sig = sk.sign(text.encode("utf-8"))
    b64u = base64.urlsafe_b64encode(sig).rstrip(b"=").decode("ascii")
    return {"signature_b64url": b64u}


@router.post("/dry_run", summary="Validate manifest and name (no write)")
def dry_run(req: InstallRequest) -> dict[str, Any]:
    """PL: Waliduje nazwę, podpis i strukturę YAML — bez zapisu.

    EN: Validates plugin name, signature and YAML structure — no write.
    """
    result: dict[str, Any] = {"ok": False, "errors": []}
    # Name & path
    safe_name = bool(re.fullmatch(r"[A-Za-z0-9_-]{1,64}", req.name))
    if not safe_name:
        result.setdefault("errors", []).append("invalid_name")
    pdir_str = str(_PLUGINS_DIR / req.name)
    if safe_name:
        try:
            pdir = (_PLUGINS_DIR / req.name).resolve()
            plugins_root = _PLUGINS_DIR.resolve()
            if not str(pdir).startswith(str(plugins_root)):
                result.setdefault("errors", []).append("invalid_path")
            pdir_str = str(pdir)
        except Exception:
            result.setdefault("errors", []).append("invalid_path")
    # Signature
    if not _verify_manifest(req.manifest_yaml, req.signature_b64u):
        result.setdefault("errors", []).append("invalid_signature")
    # YAML schema-lite
    try:
        data = yaml.safe_load(req.manifest_yaml) or {}
        mod = str(data.get("module") or "").strip()
        ver = str(data.get("version") or "").strip()
        if not mod:
            result.setdefault("errors", []).append("missing_module")
        if ver and not re.fullmatch(r"\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.\-]{1,32})?", ver):
            result.setdefault("errors", []).append("invalid_version_semver")
        result["module"] = mod
        result["version"] = ver
    except Exception:
        result.setdefault("errors", []).append("invalid_yaml")
    result["would_write_path"] = pdir_str
    result["ok"] = not result.get("errors")
    return result


@router.get("/plugin_manifest/{name}", summary="Get installed plugin manifest (YAML)")
def get_plugin_manifest(name: str) -> dict[str, str]:
    """PL: Zwraca manifest YAML zainstalowanej wtyczki (tylko lokalny odczyt).

    EN: Returns YAML manifest of an installed plugin (local read only).
    """
    if not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", name):
        raise HTTPException(status_code=400, detail="Invalid plugin name")
    p = (_PLUGINS_DIR / name / "plugin.yaml").resolve()
    root = _PLUGINS_DIR.resolve()
    try:
        if not str(p).startswith(str(root)):
            raise HTTPException(status_code=400, detail="Invalid path")
        if not p.exists():
            raise HTTPException(status_code=404, detail="Not found")
        return {"manifest_yaml": p.read_text(encoding="utf-8")}
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Read error: {e}") from e


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
