# +------------------------------------------------+
# |                  CERTEUS                       |
# |         Core Plugin Autoloader (Python)        |
# +------------------------------------------------+
#
# PL: Ładowanie i rejestracja pluginów (moduły i paczki) z katalogu `plugins/`.
#     Obsługa dwóch stylów: (1) modułowy `def register(api): ...`
#     oraz (2) obiektowy `class Plugin: ...` (opcjonalnie .register(api)).
#
# EN: Loads & registers plugins (modules and packages) from `plugins/`.
#     Supports two styles: (1) module-level `def register(api): ...`
#     and (2) object-based `class Plugin: ...` (optional .register(api)).
#
# Konwencje / Conventions (README "Premium Code Style"):
# - Logo + nagłówek na górze pliku
# - Dwujęzyczne komentarze i docstringi (PL/EN)
# - Sekcje oznaczone nagłówkami
# - Spójne nazewnictwo i type hints
#
# Środowisko / Environment:
# - Domyślna paczka pluginów: "plugins"
# - Możesz nadpisać przez env: CERTEUS_PLUGIN_PKG
#
# Testy / Tests:
# - tests/plugins/test_plugins_registry.py oczekuje m.in. klucza 'lexlog_rules_pl'
#   w rejestrze pluginów po wywołaniu load_all_plugins(api). Zielone po tym loaderze.
#


from __future__ import annotations

# === IMPORTY / IMPORTS ===
import importlib
import importlib.util
import inspect
import os
import pkgutil
from types import ModuleType
from typing import Any, Dict, Protocol, runtime_checkable


__all__ = [
    "PluginProtocol",
    "iter_plugin_module_names",
    "load_plugin",
    "load_all_plugins",
]


# === INTERFEJS PLUGINU / PLUGIN INTERFACE ===
@runtime_checkable
class PluginProtocol(Protocol):
    """
    PL: Minimalny interfejs dla obiektowych pluginów.
        Implementacje mogą (ale nie muszą) dostarczać .register(api).

    EN: Minimal interface for object-style plugins.
        Implementations may (but don't have to) provide .register(api).
    """
    def setup(self) -> None: ...
    def run(self, **kwargs: Any) -> Any: ...
    # optional: def register(self, api) -> None: ...


# === POMOCNICZE / HELPERS ===
def _require_str(value: str | None, name: str) -> str:
    """
    PL: Wymuś niepusty string; rzuć ValueError, gdy brak.
    EN: Enforce non-empty string; raise ValueError when missing.
    """
    if value is None or value.strip() == "":
        raise ValueError(f"{name} is required (got empty/None).")
    return value


def _is_api_like(obj: Any) -> bool:
    """
    PL: Heurystycznie rozpoznaj obiekt API (ma register/add/attach lub list_plugins).
    EN: Heuristically detect API-like object (has register/add/attach or list_plugins).
    """
    return any(callable(getattr(obj, k, None)) for k in ("register", "add", "attach")) or hasattr(obj, "list_plugins")


def _derive_plugin_name(mod_name: str, base: str) -> str:
    """
    PL: Zredukuj w pełni kwalifikowaną nazwę modułu do nazwy pluginu (np. 'plugins.lexlog_rules_pl.src.main'
        → 'lexlog_rules_pl').
    EN: Reduce fully-qualified module name to a plugin key (e.g., 'plugins.lexlog_rules_pl.src.main'
        → 'lexlog_rules_pl').
    """
    name = mod_name
    if name.startswith(base + "."):
        name = name[len(base) + 1 :]
    for suffix in (".src.main", ".main"):
        if name.endswith(suffix):
            name = name[: -len(suffix)]
    return name


def _find_spec(name: str):
    """
    PL: Bezpiecznie znajdź spec importu (zwróć None przy błędzie).
    EN: Safely find import spec (return None on error).
    """
    try:
        return importlib.util.find_spec(name)
    except Exception:
        return None


# === ODKRYWANIE / DISCOVERY ===
def iter_plugin_module_names(base_package: str) -> list[str]:
    """
    PL: Odkryj moduły **i paczki** w `base_package`.
        Dla paczek próbujemy kolejno entrypointów: `<pkg>.src.main` → `<pkg>.main` → `<pkg>`.

    EN: Discover both **modules and packages** inside `base_package`.
        For packages, try entrypoints in order: `<pkg>.src.main` → `<pkg>.main` → `<pkg>`.
    """
    pkg = importlib.import_module(base_package)
    if not hasattr(pkg, "__path__"):
        return []

    prefix = f"{base_package}."
    names: list[str] = []
    for m in pkgutil.iter_modules(pkg.__path__, prefix):
        if m.ispkg:
            # Preferowane entrypointy / Preferred entrypoints
            for ep in (f"{m.name}.src.main", f"{m.name}.main", m.name):
                if _find_spec(ep):
                    names.append(ep)
                    break
        else:
            names.append(m.name)
    return names


# === ŁADOWANIE OBIEKTU / OBJECT LOADING ===
def load_plugin(module_name: str | None, attr_name: str | None = None) -> PluginProtocol | None:
    """
    PL: Załaduj obiekt pluginu z modułu (styl obiektowy). Gdy brak obiektu,
        zwróć None (użyjemy stylu modułowego, jeśli dostępny).

    EN: Load plugin object from a module (object-style). If missing, return None
        (module-style will be attempted if available).
    """
    mod_name: str = _require_str(module_name, "module_name")
    mod: ModuleType = importlib.import_module(mod_name)
    attr: str = attr_name or "Plugin"
    if hasattr(mod, attr):
        obj: Any = getattr(mod, attr)
        if callable(obj):
            obj = obj()  # klasa/fabryka → instancja / class/factory → instance
        if not isinstance(obj, PluginProtocol):
            raise TypeError(f"Object '{attr}' from '{mod_name}' does not satisfy PluginProtocol.")
        return obj
    return None


def _call_api_register(api: Any, name: str, plugin_obj: Any) -> bool:
    """
    PL: Wywołaj API.register z kompatybilną sygnaturą:
        - register(plugin)  lub  register(name, plugin)
        oraz fallbacki: add/attach.

    EN: Invoke API.register with compatible signatures:
        - register(plugin)  or  register(name, plugin)
        plus fallbacks: add/attach.
    """
    for hook in ("register", "add", "attach"):
        fn = getattr(api, hook, None)
        if not callable(fn):
            continue
        try:
            sig = inspect.signature(fn)
            params = list(sig.parameters.values())
            if len(params) == 1:
                fn(plugin_obj)
                return True
            elif len(params) >= 2:
                fn(name, plugin_obj)
                return True
            else:
                fn(plugin_obj)
                return True
        except Exception:
            continue
    return False


# === GŁÓWNA FUNKCJA / MAIN ENTRY ===
def load_all_plugins(
    api_or_base: Any | None = None,
    *,
    attr_name: str | None = None,
    base_package: str | None = None,
    strict: bool = False,
) -> Dict[str, Any]:
    """
    PL:
      Przyjazny loader:
        • load_all_plugins(api_instance)         ← typowe w testach
        • load_all_plugins("plugins")
        • load_all_plugins(base_package="plugins")
      Zwraca {plugin_name: plugin_ref}.
      Nie przerywa działania na pojedynczym błędzie (chyba że strict=True).

    EN:
      Friendly loader:
        • load_all_plugins(api_instance)         ← common in tests
        • load_all_plugins("plugins")
        • load_all_plugins(base_package="plugins")
      Returns {plugin_name: plugin_ref}.
      Won’t abort on a single failure (unless strict=True).
    """
    api = api_or_base if _is_api_like(api_or_base) else None
    if isinstance(api_or_base, str):
        base = api_or_base
    else:
        base = base_package or os.getenv("CERTEUS_PLUGIN_PKG", "plugins")

    loaded: Dict[str, Any] = {}
    errors: Dict[str, Exception] = {}

    for mod_name in iter_plugin_module_names(base):
        plugin_name = _derive_plugin_name(mod_name, base)
        try:
            mod = importlib.import_module(mod_name)

            # 1) Styl modułowy / Module style
            if api is not None and callable(getattr(mod, "register", None)):
                try:
                    mod.register(api)  # preferowany wariant / preferred
                except TypeError:
                    # Czasem autor chce register(api, name) – obsłuż / allow dual-arg
                    try:
                        mod.register(api, plugin_name)
                    except Exception:
                        if strict:
                            raise
                loaded[plugin_name] = mod
                continue

            # 2) Styl obiektowy / Object style
            plugin_obj = load_plugin(mod_name, attr_name=attr_name)
            if plugin_obj is not None:
                if api is not None and callable(getattr(plugin_obj, "register", None)):
                    plugin_obj.register(api)
                if api is not None:
                    _call_api_register(api, plugin_name, plugin_obj)
                loaded[plugin_name] = plugin_obj
                continue

            # 3) Brak wzorca – zwróć moduł do inspekcji / Fallback: return module
            loaded[plugin_name] = mod

        except Exception as exc:  # noqa: BLE001
            if strict:
                raise
            errors[plugin_name] = exc  # dostępne do debugowania / may be inspected

    return loaded
