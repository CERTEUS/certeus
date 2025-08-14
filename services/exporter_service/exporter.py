# +------------------------------------------------+
# |            CERTEUS · Exporter Service          |
# |     Safe Registration Helper for Plugins       |
# +------------------------------------------------+
#
# PL: Rejestruje plugin eksportera tylko wtedy, gdy ma metodę .register(api).
#     Dzięki TypeGuard (`has_register`) Pylance nie zgłasza błędów.
#
# EN: Registers an exporter plugin only if it provides .register(api).
#     With the TypeGuard (`has_register`), Pylance is happy.

from typing import Any
from core.plugin_loader import has_register  # ✔ tylko to importujemy

def register_exporter_safely(plugin: object, api: Any) -> None:
    """
    PL: Rejestracja eksportera w sposób bezpieczny dla Pylance.
    EN: Pylance-safe exporter registration.
    """
    if has_register(plugin):
        plugin.register(api)  # ✔ po tym if-ie Pylance zna .register(api)
    else:
        # (opcjonalnie) zachowaj referencję w API lub zrób fallback
        reg = getattr(api, "register", None)
        if callable(reg):
            try:
                # nadaj sensowną nazwę, jeśli chcesz widzieć go w rejestrze
                reg("exporter_auto", plugin)
            except Exception:
                pass
