# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/run_apply_headers.py                        |

# | ROLE: Project module.                                       |

# | PLIK: scripts/run_apply_headers.py                        |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

Helper runner to execute scripts.apply_headers.main() reliably on Windows.



PL: Pomocniczy skrypt do uruchomienia scripts.apply_headers.main().

"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from importlib import import_module

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===












def main() -> None:
    mod = import_module("scripts.apply_headers")

    mod.main()


if __name__ == "__main__":
    main()





# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

