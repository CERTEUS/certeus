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



# +=====================================================================+

# |                          CERTEUS — DR                               |

# +=====================================================================+

# | FILE: dr/temporal_fortress.py                                       |

# | ROLE: Alias do skryptu TTDE 'scripts/temporal_fortress.py'.         |

# +=====================================================================+

from __future__ import annotations

from scripts.temporal_fortress import due, run  # re-export

__all__ = ["due", "run"]
