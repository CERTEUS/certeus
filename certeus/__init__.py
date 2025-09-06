# +=====================================================================+
# |                          CERTEUS — HEART                            |
# +=====================================================================+
# | FILE: certeus/__init__.py                                           |
# | ROLE:                                                               |
# |  PL: Plik inicjalizacji głównego pakietu CERTEUS                    |
# |  EN: Main CERTEUS package initialization file                       |
# +=====================================================================+

"""CERTEUS - Proof-Driven Autonomy System."""

__version__ = "0.0.1"
__author__ = "CERTEUS Team"
__description__ = "CERTEUS – Proof-Driven Autonomy (skeleton)"

# Re-export core modules for easy access
from core import api, omega_jurisdiction, version

__all__ = ["api", "omega_jurisdiction", "version"]
