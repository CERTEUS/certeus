# +-------------------------------------------------------------+
# |                   CERTEUS - LEXLOG (PL) Plugin              |
# +-------------------------------------------------------------+
# | PLIK / FILE: plugins/lexlog_rules_pl/src/main.py            |
# | ROLA / ROLE: Przykładowy plugin rejestrujący reguły LEXLOG. |
# |              Sample plugin registering LEXLOG rules.        |
# +-------------------------------------------------------------+

from __future__ import annotations

from typing import Any, Final

PLUGIN_NAME: Final[str] = "lexlog_rules_pl"


class Plugin:
    """
    PL: Minimalna implementacja pluginu. W realnym wdrożeniu trzyma tu
        kompilowane reguły LEXLOG, walidatory itd.
    EN: Minimal plugin implementation. In production, keep compiled
        LEXLOG rules, validators, etc.
    """

    def __init__(self) -> None:
        self.ruleset_version: str = "pl.lexlog/1.0.0"

    def setup(self) -> None:
        # PL: Tu mógłbyś załadować reguły z packs/jurisdictions/PL/rules/
        # EN: Load rules here from packs/jurisdictions/PL/rules/
        pass

    def run(self, **kwargs: Any) -> dict[str, Any]:
        return {"status": "ok", "plugin": PLUGIN_NAME, "rules": self.ruleset_version, "kwargs": kwargs}

    def register(self, api: Any) -> None:
        """
        PL: Rejestracja w rdzeniowym API: obsłuż API.register(plugin) i API.register(name, plugin).
        EN: Register into core API: support API.register(plugin) and API.register(name, plugin).
        """
        hook = getattr(api, "register", None) or getattr(api, "add", None) or getattr(api, "attach", None)
        if not callable(hook):
            raise RuntimeError("Plugin API lacks register/add/attach method")
        try:
            hook(self)  # register(plugin)
        except TypeError:
            hook(PLUGIN_NAME, self)  # register(name, plugin)


def register(api: Any, name: str | None = None) -> None:
    """
    PL: Styl modułowy (używany przez loader, jeśli w plugin.yaml podasz 'register: register').
    EN: Module-level style (used by loader when 'register: register' in plugin.yaml).
    """
    plugin = Plugin()
    plugin.setup()
    hook = getattr(api, "register", None) or getattr(api, "add", None) or getattr(api, "attach", None)
    if not callable(hook):
        raise RuntimeError("Plugin API lacks register/add/attach method")
    if name is not None:
        try:
            hook(name, plugin)
            return
        except TypeError:
            pass
    try:
        hook(plugin)
    except TypeError:
        hook(PLUGIN_NAME, plugin)
