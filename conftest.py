#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: conftest.py                                         |
# | ROLE: PyTest bootstrap.                                     |
# | PLIK: conftest.py                                         |
# | ROLA: Inicjalizacja ustawień Hypothesis dla CI.            |
# +-------------------------------------------------------------+
"""
Globalne ustawienia testów.

- Stabilizujemy Hypothesis (właściwości): wyłączamy healthcheck "too_slow",
  bo część strategii używa filtrów powodujących odrzucenia i dłuższy czas generacji.
"""

from __future__ import annotations

from hypothesis import HealthCheck, settings

# Profil CI: eliminujemy fałszywe alarmy na wolne generowanie wejść
settings.register_profile("ci", suppress_health_check=[HealthCheck.too_slow])
settings.load_profile("ci")
