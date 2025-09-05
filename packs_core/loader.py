"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: packs_core/loader.py                                |

# | ROLE: Project module.                                       |

# | PLIK: packs_core/loader.py                                |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

from dataclasses import dataclass
from importlib import import_module
from pathlib import Path
from typing import Any, Protocol

import yaml  # type: ignore

@dataclass(slots=True)
class PackInfo:
    name: str
    abi: str
    caps: list[str]
    version: str | None = None
    enabled: bool = True

class PackLike(Protocol):
    def handle(self, kind: str, payload: dict[str, Any]) -> Any: ...

def _plugin_root() -> Path:
    return Path(__file__).resolve().parents[1] / "plugins"

def _read_manifest(p: Path) -> dict[str, Any] | None:
    try:
        data = yaml.safe_load(p.read_text(encoding="utf-8"))  # nosec: config file
        if isinstance(data, dict):
            return data
    except Exception:
        return None
    return None

def discover() -> list[PackInfo]:
    """
    Skanuje `plugins/*/plugin.yaml` i zwraca podstawowe metadane.
    ABI: python:<module> jeśli dostępny moduł, inaczej "python".
    Caps: z manifestu (capabilities) albo pusty.
    """
    root = _plugin_root()
    if not root.exists():
        return []
    infos: list[PackInfo] = []
    for man in root.glob("*/plugin.yaml"):
        data = _read_manifest(man) or {}
        name = str(data.get("name") or man.parent.name)
        module = str(data.get("module") or "")
        abi = f"python:{module}" if module else "python"
        caps = list(data.get("capabilities") or [])
        version = str(data.get("version") or data.get("ver") or "") or None
        enabled = bool(data.get("enabled", True))
        infos.append(PackInfo(name=name, abi=abi, caps=caps, version=version, enabled=enabled))
    return infos

def load(path: str) -> PackLike:  # noqa: A002 - zgodność z istniejącymi importami
    """
    Ładuje paczkę po nazwie (plugins/<name>/plugin.yaml) albo module path.
    Oczekuje, że moduł posiada `register()` zwracający obiekt z metodą `handle(kind, payload)`
    lub klasę `Plugin` z metodą `register(api)` zwracającą obiekt z `handle`.
    """
    module_path = ""
    if "." in path:
        module_path = path
    else:
        man = _plugin_root() / path / "plugin.yaml"
        data = _read_manifest(man) or {}
        module_path = str(data.get("module") or "")
        if not module_path:
            # Spróbuj konwencji adapter.py
            mod_guess = f"plugins.{path}.adapter"
            try:
                import_module(mod_guess)
                module_path = mod_guess
            except Exception as e:
                raise RuntimeError(f"No module for pack '{path}': {e}") from e
    try:
        mod = import_module(module_path)
    except Exception as e:
        raise RuntimeError(f"Cannot import module '{module_path}': {e}") from e

    reg = getattr(mod, "register", None)
    if callable(reg):
        pack = reg()
        if not hasattr(pack, "handle"):
            raise RuntimeError("Pack register() did not return handle-capable object")
        return pack  # type: ignore[return-value]
    Plugin = getattr(mod, "Plugin", None)
    if Plugin is not None:
        inst = Plugin()
        if hasattr(inst, "register"):
            api = object()
            pack = inst.register(api)
            if not hasattr(pack, "handle"):
                raise RuntimeError("Plugin.register did not return handle-capable object")
            return pack  # type: ignore[return-value]
    raise RuntimeError(f"Unsupported pack module shape for '{module_path}'")
