#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: sdk/python/certeus_sdk/__init__.py                  |
# | ROLE: Project module.                                       |
# | PLIK: sdk/python/certeus_sdk/__init__.py                  |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: SDK Python dla CERTEUS (MVP): klient synchronizowany do QTMP i lexqft.
EN: Python SDK for CERTEUS (MVP): synchronous client for QTMP and lexqft.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from .client import CerteusClient, SDKResponse

__all__ = ["CerteusClient", "SDKResponse"]
