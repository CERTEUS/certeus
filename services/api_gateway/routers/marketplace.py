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

from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field
import yaml

from core.plugin_loader import _discover_plugins as discover_plugins  # type: ignore[attr-defined]
from packs_core.loader import PackInfo, discover as discover_packs
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
                module=str(getattr(spec, "module", None)) if getattr(spec, "module", None) else None,
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

    pdir = _PLUGINS_DIR / req.name
    pdir.mkdir(parents=True, exist_ok=True)
    (pdir / "plugin.yaml").write_text(req.manifest_yaml, encoding="utf-8")
    return {"ok": True, "name": req.name, "path": str(pdir)}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
