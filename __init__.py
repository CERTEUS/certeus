# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: __init__.py                                                   |
# | ROLE:                                                               |
# |  PL: Główny plik inicjalizacji pakietu CERTEUS                      |
# |  EN: Main CERTEUS package initialization file                       |
# +=====================================================================+

"""CERTEUS - Proof-Driven Autonomy System."""

__version__ = "0.0.1"
__author__ = "CERTEUS Team"
__description__ = "CERTEUS – Proof-Driven Autonomy (skeleton)"

# Import main modules
from . import core, services

__all__ = ["core", "services"]
