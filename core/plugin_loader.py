# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: core/plugin_loader.py                               |

# | ROLE: Project module.                                       |

# | PLIK: core/plugin_loader.py                               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""
PL: Ładowanie wtyczek (Domain Packs) i rejestracja zdolności.

EN: Plugin loader (Domain Packs) and capability registry.
"""


# +-------------------------------------------------------------+


# |                    CERTEUS - Plugin Loader                  |


# +-------------------------------------------------------------+


# | PLIK / FILE: core/plugin_loader.py                          |


# | ROLA / ROLE: Wyszukuje i ładuje pluginy z katalogu          |


# |              'plugins/<name>/{plugin.yaml, src/main.py}'.   |


# |              Scans & loads plugins from the canonical tree. |


# +-------------------------------------------------------------+

from __future__ import annotations

from dataclasses import dataclass
import importlib
import logging
import os
from pathlib import Path
from typing import Any

try:
    import yaml  # PyYAML (preferowane)


except Exception:  # pragma: no cover
    yaml = None  # type: ignore[assignment]


log = logging.getLogger("certeus.plugins")


if not log.handlers:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(name)s: %(message)s")


# === KONFIG / CONFIG ===


REPO_ROOT = Path(__file__).resolve().parents[1]


PLUGINS_DIR = REPO_ROOT / "plugins"


# Dopuszczamy entrypointy:


# - moduł:  module: "plugins.lexlog_rules_pl.src.main"


# - opcjonalnie: register: "register"  (funkcja)


#   w braku: class Plugin z metodą register(api)


@dataclass(frozen=True, slots=True)
class PluginSpec:
    name: str

    module: str

    register: str | None = None

    enabled: bool = True

    version: str | None = None


def _parse_plugin_yaml(path: Path) -> PluginSpec | None:
    """PL: Parsuje plugin.yaml → PluginSpec. EN: Parse plugin.yaml → PluginSpec."""

    try:
        raw = path.read_text(encoding="utf-8")

    except FileNotFoundError:
        return None

    data: dict[str, Any]

    if yaml:
        data = yaml.safe_load(raw) or {}

    else:  # fallback na prosty parser klucz: wartość
        data = {}

        for line in raw.splitlines():
            line = line.strip()

            if not line or line.startswith("#") or ":" not in line:
                continue

            k, v = line.split(":", 1)

            data[k.strip()] = v.strip().strip("'\"")

    name = str(data.get("name") or path.parent.name)

    module = str(data.get("module") or "")

    register = str(data["register"]) if "register" in data else None

    enabled = bool(data.get("enabled", True))

    version = data.get("version")

    if not module:
        log.warning("Plugin '%s' has empty 'module' in %s", name, path)

        return None

    return PluginSpec(name=name, module=module, register=register, enabled=enabled, version=version)


def _discover_plugins(base_dir: Path = PLUGINS_DIR) -> list[PluginSpec]:
    """PL: Znajdź wszystkie plugin.yaml. EN: Find all plugin.yaml files."""

    specs: list[PluginSpec] = []

    if not base_dir.exists():
        log.info("Plugins dir not found: %s", base_dir)

        return specs

    for plugin_root in sorted(base_dir.iterdir()):
        if not plugin_root.is_dir():
            continue

        yml = plugin_root / "plugin.yaml"

        spec = _parse_plugin_yaml(yml)

        if spec and spec.enabled:
            specs.append(spec)

    return specs


def _import_module(module_path: str) -> Any:
    """PL/EN: Import by module path (importlib)."""

    return importlib.import_module(module_path)


def _register_into_api(api: Any, spec: PluginSpec, mod: Any) -> str | None:
    """







    PL: Próbuje wywołać rejestrację; wspiera:







        - funkcję module-level: register(api[, name])







        - klasę Plugin z metodą register(api)







        - API.register(plugin) lub API.register(name, plugin)







    EN: Perform registration via module function or Plugin class.







    """

    # 1) Preferuj module-level register(...)

    if spec.register and hasattr(mod, spec.register):
        fn = getattr(mod, spec.register)

        try:
            fn(api, spec.name)  # register(api, name)

        except TypeError:
            fn(api)  # register(api)

        return spec.name

    # 2) Szukaj klasy Plugin z metodą register(api)

    plugin_obj = None

    if hasattr(mod, "Plugin"):
        try:
            plugin_obj = mod.Plugin()  # type: ignore[call-arg]

        except Exception as e:  # pragma: no cover
            log.warning("Cannot instantiate Plugin() for %s: %s", spec.name, e)

    if plugin_obj and hasattr(plugin_obj, "register"):
        hook = getattr(api, "register", None) or getattr(api, "add", None) or getattr(api, "attach", None)

        if not callable(hook):
            raise RuntimeError("Plugin API is missing a register/add/attach method")

        try:
            hook(plugin_obj)  # API.register(plugin)

        except TypeError:
            hook(spec.name, plugin_obj)  # API.register(name, plugin)

        return spec.name

    # 3) Brak znanego sposobu rejestracji

    log.warning("Plugin '%s' has neither register() nor Plugin.register()", spec.name)

    return None


def load_all_plugins(api: Any) -> list[str]:
    """







    PL: Ładuje wszystkie pluginy i rejestruje je w przekazanym API.







    EN: Loads all plugins and registers them into the provided API.







    """

    # Umożliwiamy wskazanie innego pakietu/katalogu (np. do testów) przez ENV

    custom_dir = os.getenv("CERTEUS_PLUGINS_DIR")

    base_dir = Path(custom_dir) if custom_dir else PLUGINS_DIR

    loaded: list[str] = []

    for spec in _discover_plugins(base_dir):
        try:
            mod = _import_module(spec.module)

            name = _register_into_api(api, spec, mod)

            if name:
                loaded.append(name)

                log.info("Plugin loaded: %s (%s)", name, spec.module)

        except ModuleNotFoundError as e:
            log.warning("Module not found for plugin '%s': %s", spec.name, e)

        except Exception as e:  # pragma: no cover
            log.warning("Failed to load plugin '%s': %s", spec.name, e)

    return loaded


# --- Helpery do introspekcji punktu rejestracji pluginu / Plugin registration helpers ---


def has_register(candidate: Any) -> bool:
    """







    PL: Sprawdza, czy obiekt/moduł udostępnia punkt rejestracji pluginu.







        Wspierane style:







          1) Funkcja modułowa:    register(api)







          2) Klasa Plugin:        class Plugin: def register(self, api) -> None







    EN: Checks whether the given object/module exposes a plugin registration entrypoint.







        Supported styles:







          1) Module-level function: register(api)







          2) Plugin class:          class Plugin: def register(self, api) -> None







    """

    try:
        reg = getattr(candidate, "register", None)

        if callable(reg):
            return True

        plugin_cls = getattr(candidate, "Plugin", None)

        if plugin_cls is not None and callable(getattr(plugin_cls, "register", None)):
            return True

        return False

    except Exception:
        return False


# Zadeklaruj publiczny interfejs modułu / Public module API


__all__ = ["PluginSpec", "load_all_plugins", "has_register"]
