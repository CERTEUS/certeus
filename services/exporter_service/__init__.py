# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/exporter_service/__init__.py                 |
# | ROLE: Exporter service package export                       |
# | PLIK: services/exporter_service/__init__.py                 |
# | ROLA: Pakiet eksportera — publiczne API pakietu             |
# +-------------------------------------------------------------+

"""
CERTEUS — Exporter Service Package
PL: Publiczne API pakietu eksportera raportów (eksport ExporterService).
EN: Public API of the exporter package (exports ExporterService).
"""

from .exporter import ExporterService

__all__ = ["ExporterService"]
