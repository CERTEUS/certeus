#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: clients/python/certeus_sdk/__init__.py               |
# | ROLE: Python SDK public API                                 |
# | PLIK: clients/python/certeus_sdk/__init__.py               |
# | ROLA: Publiczne API SDK w Pythonie                          |
# +-------------------------------------------------------------+
"""
PL: Minimalne SDK dla CERTEUS w Pythonie (HTTP wrapper nad API Gateway).

EN: Minimal Python SDK for CERTEUS (HTTP wrapper over the API Gateway).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from .client import CerteusClient

__all__ = ["CerteusClient"]

# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
