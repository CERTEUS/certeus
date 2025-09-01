# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/law_as_data/__init__.py                    |

# | ROLE: Project module.                                       |

# | PLIK: services/law_as_data/__init__.py                    |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from .cache import FileCache, cache_from_uri, compute_digest

__all__ = [
    "FileCache",
    "cache_from_uri",
    "compute_digest",
]
