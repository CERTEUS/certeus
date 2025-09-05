# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/conftest.py                                   |

# | ROLE: Project module.                                       |

# | PLIK: tests/conftest.py                                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Zbiór współdzielonych fikstur i pomocników testowych dla całego pakietu testów.

EN: Shared pytest fixtures and helpers used across the test suite.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from pathlib import Path
import sys

from hypothesis import HealthCheck, settings

ROOT = Path(__file__).resolve().parents[1]

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

# Hypothesis global profile for CI/local: relax deadlines to avoid flakes
settings.register_profile(
    "ci",
    deadline=1000,
    suppress_health_check=(HealthCheck.too_slow,),
)
settings.load_profile("ci")
