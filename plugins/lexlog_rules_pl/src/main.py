# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/plugins/lexlog_rules_pl/src/main.py     |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: plugins/lexlog_rules_pl/src/main.py                 |

# | ROLE: Project module.                                       |

# | PLIK: plugins/lexlog_rules_pl/src/main.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""



PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.



EN: CERTEUS module – please complete the functional description.



"""


# +-------------------------------------------------------------+


# |                   CERTEUS - LEXLOG (PL) Plugin              |


# +-------------------------------------------------------------+


# | PLIK / FILE: plugins/lexlog_rules_pl/src/main.py            |


# | ROLA / ROLE: Przykładowy plugin rejestrujący reguły LEXLOG. |


# |              Sample plugin registering LEXLOG rules.        |


# +-------------------------------------------------------------+

from __future__ import annotations

from collections.abc import MutableMapping
from typing import Any, Final

PLUGIN_NAME: Final[str] = "lexlog_rules_pl"


def _safe_register(api: Any, plugin: Any, name: str) -> None:
    """



    PL: Rejestracja odporna na różne interfejsy API.



        Obsługujemy kolejno:



          • register_plugin(name, plugin)



          • add_plugin(name, plugin)



          • register(plugin) / register(name, plugin)



          • add(plugin)      / add(name, plugin)



          • attach(plugin)   / attach(name, plugin)



        Fallback: mapy typu api.plugins / api.registry / api.plugin_registry.







    EN: Registration resilient to various API shapes.



        We support, in order:



          • register_plugin(name, plugin)



          • add_plugin(name, plugin)



          • register(plugin) / register(name, plugin)



          • add(plugin)      / add(name, plugin)



          • attach(plugin)   / attach(name, plugin)



        Fallback: dict-like registries api.plugins / api.registry / api.plugin_registry.



    """

    candidates: list[tuple[str, tuple[Any, ...]]] = [
        ("register_plugin", (name, plugin)),
        ("add_plugin", (name, plugin)),
        ("register", (plugin,)),
        ("register", (name, plugin)),
        ("add", (plugin,)),
        ("add", (name, plugin)),
        ("attach", (plugin,)),
        ("attach", (name, plugin)),
    ]

    for method, args in candidates:
        fn = getattr(api, method, None)

        if callable(fn):
            try:
                fn(*args)

                return

            except TypeError:
                # Spróbuj kolejny wariant sygnatury

                continue

    # Fallback: bezpośrednie wpisanie do mapy rejestru

    for attr in ("plugins", "registry", "plugin_registry"):
        reg = getattr(api, attr, None)

        if isinstance(reg, dict) or isinstance(reg, MutableMapping):
            reg[name] = plugin

            return

    raise RuntimeError("No compatible registration hook or registry mapping found on Plugin API")


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
        return {
            "status": "ok",
            "plugin": PLUGIN_NAME,
            "rules": self.ruleset_version,
            "kwargs": kwargs,
        }

    def register(self, api: Any) -> None:
        """



        PL: Rejestracja w rdzeniu – odporna na różne kształty API.



        EN: Core registration – resilient to various API shapes.



        """

        _safe_register(api, self, PLUGIN_NAME)


def register(api: Any, name: str | None = None) -> None:
    """



    PL: Styl modułowy (używany przez loader, jeśli w plugin.yaml podasz 'register: register').



    EN: Module-level style (used by loader when 'register: register' is present in plugin.yaml).



    """

    plugin = Plugin()

    plugin.setup()

    _safe_register(api, plugin, name or PLUGIN_NAME)
