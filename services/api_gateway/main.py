# +-------------------------------------------------------------+
# |                      CERTEUS - API Gateway                  |
# +-------------------------------------------------------------+
# | PLIK / FILE: services/api_gateway/main.py                   |
# | ROLA / ROLE: Główny punkt wejściowy FastAPI; dołącza        |
# |              routery i udostępnia endpointy globalne.       |
# |              Main FastAPI entrypoint; mounts routers and    |
# |              exposes global endpoints.                      |
# +-------------------------------------------------------------+

from __future__ import annotations

import logging
from contextlib import asynccontextmanager
from typing import Any, Protocol, cast
from collections.abc import Iterable, Mapping

from fastapi import FastAPI

# ✅ Poprawne importy: PluginAPI z core.api, loader z core.plugin_loader
try:
    from core.api import PluginAPI  # ← tu jest PluginAPI
    from core.plugin_loader import load_all_plugins
except Exception as e:  # pragma: no cover
    PluginAPI = None  # type: ignore[assignment]
    load_all_plugins = None  # type: ignore[assignment]
    logging.getLogger("certeus.api").warning("Plugin system not available: %s", e)

# (Opcjonalnie) router księgi
try:
    from services.api_gateway.routers.ledger import router as ledger_router  # type: ignore
except Exception:  # pragma: no cover
    ledger_router = None  # type: ignore[assignment]

log = logging.getLogger("certeus.api")
if not log.handlers:  # idempotent
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(name)s: %(message)s")


# === PROTOKÓŁ DLA TYPE CHECKERA / TYPE-CHECKER PROTOCOL ===
class _PluginAPIProto(Protocol):
    """
    PL: Minimalne API: zwróć listę nazw pluginów (Iterable[str]) lub mapping {name: obj}.
    EN: Minimal API: return plugin names as Iterable[str] or a mapping {name: obj}.
    """
    def list_plugins(self) -> Iterable[str] | Mapping[str, Any]: ...


def _normalize_plugin_names(raw: Iterable[str] | Mapping[str, Any]) -> list[str]:
    """
    PL: Zamienia Iterable[str] lub Mapping[str, Any] na list[str] nazw.
    EN: Converts Iterable[str] or Mapping[str, Any] into list[str] of names.
    """
    if isinstance(raw, Mapping):
        return list(raw.keys())
    return list(raw)


# === LIFE SPAN: start/stop serwisu ===
@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    PL: Przy starcie inicjalizujemy system pluginów i wpinamy go do app.state.
    EN: On startup, initialize plugin system and attach it to app.state.
    """
    if PluginAPI and load_all_plugins:
        api = PluginAPI()
        app.state.plugin_api = api  # type: ignore[attr-defined]
        try:
            load_all_plugins(api)
            pa = cast(_PluginAPIProto, api)
            plugin_names: list[str] = _normalize_plugin_names(pa.list_plugins())
            log.info("Plugins loaded: %s", plugin_names)
        except Exception as exc:  # pragma: no cover
            log.warning("Plugin loading failed/skipped: %s", exc)
    else:
        log.info("Starting without plugin system.")
    yield
    # (tu ewentualny graceful shutdown)


# === APLIKACJA ===
app = FastAPI(
    title="CERTEUS - Verifiable Cognitive Intelligence API",
    description=(
        "API dla systemu CERTEUS. Zapewnia dostęp do Silnika Prawdy, "
        "Silnika Kreacji i Architektury Zaufania."
    ),
    version="0.1.0",
    lifespan=lifespan,
)

# === ROUTERY ===
if ledger_router is not None:
    app.include_router(ledger_router, prefix="/ledger", tags=["Ledger"])

# === ENDPOINTY GLOBALNE ===
@app.get("/health", tags=["System"])
def health_check() -> dict[str, Any]:
    """
    PL: Prosty endpoint do sprawdzania kondycji usługi.
    EN: Simple liveness endpoint.
    """
    plugins: list[str] | None = None
    api = getattr(app.state, "plugin_api", None)
    if api is not None:
        try:
            pa = cast(_PluginAPIProto, api)
            plugins = _normalize_plugin_names(pa.list_plugins())
        except Exception:  # pragma: no cover
            plugins = None
    return {"status": "ok", "message": "CERTEUS API is alive and well.", "plugins": plugins}
