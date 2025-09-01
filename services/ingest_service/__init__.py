# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/ingest_service/__init__.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/ingest_service/__init__.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Pakiet serwisu ingestii. Ten moduł oznacza pakiet Pythona oraz

    udostępnia publiczny interfejs (eksport) najczęściej używanych typów.

EN: Ingestion service package. This module marks the Python package and

    exposes a public interface (exports) of the most commonly used types.

"""

# === IMPORTY / IMPORTS ===
from .models import Fact, FactRole

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


# [BLOCK: PUBLIC API EXPORTS / EKSPORT INTERFEJSU PUBLICZNEGO]


__all__ = ["Fact", "FactRole"]


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
