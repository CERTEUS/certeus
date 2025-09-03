# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/proof_verifier/__init__.py                 |

# | ROLE: Project module.                                       |

# | PLIK: services/proof_verifier/__init__.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===

from .verifier import verify_drat, verify_lfsc

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

__all__ = ["verify_lfsc", "verify_drat"]

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
