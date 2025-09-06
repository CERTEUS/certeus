# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/plugins/test_plugins_registry.py              |

# | ROLE: Project module.                                       |

# | PLIK: tests/plugins/test_plugins_registry.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

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

# | FILE: tests/plugins/test_plugins_registry.py              |

# | ROLE: Project module.                                       |

# | PLIK: tests/plugins/test_plugins_registry.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

# +------------------------------------------------+

# |                  CERTEUS                       |

# |                Core Plugin API                 |

# +------------------------------------------------+

#

# PL: Minimalne API rdzenia do rejestracji pluginów oraz

#     rejestrów funkcjonalnych (adapters/exporters).

#

# EN: Minimal core API for plugin registration and

#     functional registries (adapters/exporters).

#

# Konwencje (README "Premium Code Style"):

# - Logo, dwujęzyczne komentarze, sekcje, type hints.

#

from __future__ import annotations

from typing import Any


class PluginAPI:
    """

    PL: Prosty rejestr pluginów i entrypointów funkcjonalnych.

        - register(plugin) lub register(name, plugin)

        - adapters/exporters jako słowniki funkcji/obiektów

    EN: Simple registry for plugins and functional entrypoints.

        - register(plugin) or register(name, plugin)

        - adapters/exporters as dicts of callables/objects

    """

    def __init__(self) -> None:
        # === STAN / STATE ===

        self._plugins: dict[str, object] = {}

        self.adapters: dict[str, object] = {}

        self.exporters: dict[str, object] = {}

    # === REJESTRACJA PLUGINU / PLUGIN REGISTRATION ===

    def register(self, *args: Any) -> None:
        """

        PL: Obsługuje dwie sygnatury:

            • register(plugin)

            • register(name, plugin)

        EN: Supports two signatures:

            • register(plugin)

            • register(name, plugin)

        """

        if len(args) == 1:
            plugin = args[0]

            # Nazwa z atrybutów lub modułu / Name from attrs or module

            name = getattr(plugin, "name", None) or getattr(plugin, "__plugin_name__", None)

            if not name:
                mod = getattr(plugin, "__module__", "")

                # Utnij końcówkę .src.main jeżeli występuje / trim .src.main suffix

                if mod.endswith(".src.main"):
                    parts = mod.split(".")

                    # … ['plugins', '<name>', 'src', 'main'] → weź index -3

                    name = parts[-3] if len(parts) >= 3 else parts[-1]

                else:
                    name = mod.split(".")[-1] if mod else plugin.__class__.__name__

        else:
            name, plugin = args[0], args[1]

        self._plugins[str(name)] = plugin

    # === PODGLĄD / INTROSPECTION ===

    def list_plugins(self):
        """

        PL: Zwróć widok kluczy (dict_keys), zgodnie z oczekiwaniem testów.

        EN: Return keys view (dict_keys), as tests expect.

        """

        return self._plugins.keys()

    # === REJESTRY FUNKCYJNE / FUNCTIONAL REGISTRIES ===

    def register_adapter(self, key: str, fn: object) -> None:
        """PL: Zarejestruj adapter (np. isap.pl.snapshot). EN: Register adapter."""

        self.adapters[key] = fn

    def register_exporter(self, key: str, fn: object) -> None:
        """PL: Zarejestruj eksporter (np. pl.exporter.docx_pdf). EN: Register exporter."""

        self.exporters[key] = fn
