# +------------------------------------------------+
# |                  CERTEUS                       |
# |            Core Plugin Autoloader (Py)         |
# +------------------------------------------------+
#
# PL: Autoload pluginów z pakietu `plugins`, wsparcie:
#     • styl modułowy:    def register(api): ...
#     • styl obiektowy:   class Plugin: ...  (opcjonalnie .register(api))
#     Z Pylance/Mypy współpracujemy przez Protocol + TypeGuard.
#
# EN: Autoload plugins from the `plugins` package, supporting:
#     • module style:     def register(api): ...
#     • object style:     class Plugin: ...  (optional .register(api))
#     Pylance/Mypy happy via Protocol + TypeGuard.
#
# Konwencje (README):
# - Dwujęzyczne komentarze, czytelne nagłówki, type hints.
# - Brak shadowingu nazw klas (nie mylimy PluginAPI z protokołem pluginu).
#

from __future__ import annotations

# === IMPORTS ===
import importlib
import importlib.util
import inspect
import os
import pkgutil
from types import ModuleType
from typing import Any, Dict, Protocol, runtime_checkable, TypeGuard


__all__ = [
    "BasePluginProtocol",
    "RegisterablePluginProtocol",
    "has_register",
    "iter_plugin_module_names",
    "load_plugin",
    "load_all_plugins",
]


# === PLUGIN PROTOCOLS (PL/EN) ===
@runtime_checkable
class BasePluginProtocol(Protocol):
    """
    PL: Minimalny rdzeń zachowania pluginu (bez rejestracji do API).
    EN: Minimal core behavior of a plugin (without API registration).
    """
    def setup(self) -> None: ...
    def run(self, **kwargs: Any) -> Any: ...


@runtime_checkable
class RegisterablePluginProtocol(BasePluginProtocol, Protocol):
    """
    PL: Plugin, który potrafi zarejestrować się w API (ma .register(api)).
    EN: Plugin that can self-register into API (has .register(api)).
    """
    def register(self, api: Any) -> None: ...


def has_register(obj: object) -> TypeGuard[RegisterablePluginProtocol]:
    """
    PL: Strażnik typu — po `if has_register(x):` Pylance/Mypy wie, że `x.register(api)` istnieje.
    EN: Type guard — after `if has_register(x):`, Pylance/Mypy knows `x.register(api)` exists.
    """
    return callable(getattr(obj, "register", None))


# === HELPERS ===
def _require_str(value: str | None, name: str) -> str:
    """PL: Wymuś niepusty string. EN: Enforce non-empty string."""
    if value is None or value.strip() == "":
        raise ValueError(f"{name} is required (got empty/None).")
    return value


def _find_spec(name: str):
    """PL/EN: Safe spec lookup (None on failure)."""
    try:
        return importlib.util.find_spec(name)
    except Exception:
        return None


def _is_api_like(obj: Any) -> bool:
    """
    PL: Heurystyka: czy to „API” (ma register/add/attach lub list_plugins)?
    EN: Heuristic: is this an API-like object (has register/add/attach or list_plugins)?
    """
    return any(callable(getattr(obj, k, None)) for k in ("register", "add", "attach")) or hasattr(obj, "list_plugins")


def _derive_plugin_name(mod_name: str, base: str) -> str:
    """
    PL: Z 'plugins.pkg.src.main' → 'pkg'; zdejmuje prefix i sufiksy.
    EN: From 'plugins.pkg.src.main' → 'pkg'; strips prefix and suffixes.
    """
    name = mod_name
    if name.startswith(base + "."):
        name = name[len(base) + 1 :]
    for suffix in (".src.main", ".main"):
        if name.endswith(suffix):
            name = name[: -len(suffix)]
    return name


# === DISCOVERY ===
def iter_plugin_module_names(base_package: str) -> list[str]:
    """
    PL: Odkryj moduły **i paczki** w `base_package`.
        Dla paczek próbujemy entrypointów: `<pkg>.src.main` → `<pkg>.main` → `<pkg>`.

    EN: Discover both **modules and packages** inside `base_package`.
        For packages, try entrypoints: `<pkg>.src.main` → `<pkg>.main` → `<pkg>`.
    """
    pkg = importlib.import_module(base_package)
    if not hasattr(pkg, "__path__"):
        return []

    prefix = f"{base_package}."
    names: list[str] = []
    for m in pkgutil.iter_modules(pkg.__path__, prefix):
        if m.ispkg:
            for ep in (f"{m.name}.src.main", f"{m.name}.main", m.name):
                if _find_spec(ep):
                    names.append(ep)
                    break
        else:
            names.append(m.name)
    return names


# === LOADING ===
def load_plugin(module_name: str | None, attr_name: str | None = None) -> BasePluginProtocol | None:
    """
    PL: Załaduj obiekt pluginu (styl obiektowy). Brak obiektu → None (spróbujemy styl modułowy).

    EN: Load plugin object (object style). If missing → None (module style will be tried).
    """
    mod_name: str = _require_str(module_name, "module_name")
    mod: ModuleType = importlib.import_module(mod_name)
    attr: str = attr_name or "Plugin"
    if hasattr(mod, attr):
        obj: Any = getattr(mod, attr)
        if callable(obj):
            obj = obj()  # klasa/fabryka → instancja / class/factory → instance
        if not isinstance(obj, BasePluginProtocol):
            # Nie blokuj ostro — pozwól działać, ale daj komunikat wyżej.
            raise TypeError(f"Object '{attr}' from '{mod_name}' does not satisfy BasePluginProtocol.")
        return obj
    return None


def _call_api_register(api: Any, name: str, plugin_obj: Any) -> bool:
    """
    PL: Wywołaj API.register z różnymi sygnaturami (register(plugin) || register(name, plugin)),
        z fallbackami add/attach.

    EN: Invoke API.register with various signatures (register(plugin) || register(name, plugin)),
        with add/attach fallbacks.
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


# === MAIN ENTRY ===
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
        • load_all_plugins(api_instance)         ← typowo w testach
        • load_all_plugins("plugins")
        • load_all_plugins(base_package="plugins")
      Zwraca {plugin_name: plugin_ref}. strict=True → wyjątek przy 1. błędzie.

    EN:
      Friendly loader:
        • load_all_plugins(api_instance)         ← common in tests
        • load_all_plugins("plugins")
        • load_all_plugins(base_package="plugins")
      Returns {plugin_name: plugin_ref}. strict=True → raise on first failure.
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

            # 1) Module style: def register(api): ...
            if api is not None and callable(getattr(mod, "register", None)):
                try:
                    mod.register(api)  # preferowane
                except TypeError:
                    # niektórzy chcą register(api, name) — obsłuż
                    try:
                        mod.register(api, plugin_name)
                    except Exception:
                        if strict:
                            raise
                loaded[plugin_name] = mod
                continue

            # 2) Object style: class Plugin: ...
            plugin_obj = load_plugin(mod_name, attr_name=attr_name)
            if plugin_obj is not None:
                if api is not None and has_register(plugin_obj):
                    plugin_obj.register(api)  # ← Pylance OK dzięki TypeGuard
                if api is not None:
                    _call_api_register(api, plugin_name, plugin_obj)
                loaded[plugin_name] = plugin_obj
                continue

            # 3) Fallback: zwróć moduł do inspekcji
            loaded[plugin_name] = mod

        except Exception as exc:  # noqa: BLE001
            if strict:
                raise
            errors[plugin_name] = exc  # do ewentualnego logowania

    return loaded
