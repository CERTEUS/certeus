#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/cfe/__init__.py                             |
# | ROLE: Project module.                                       |
# | PLIK: services/cfe/__init__.py                             |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Pakiet CFE (geometria sensu): metryka grafowa, krzywizny Ricciego,
    proste geodezyjne oraz horyzont (lock) — implementacje wspólne
    dla routera API.

EN: CFE package (geometry of meaning): graph metric, Ricci curvatures,
    simple geodesics and horizon (lock) — shared implementations used by
    the API router.
"""

# === IMPORTY / IMPORTS ===

from .metric import CurvatureSummary as CurvatureSummary, kappa_max_for_case as kappa_max_for_case  # re-export helpers

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
