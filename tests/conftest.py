# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/conftest.py                                     |
# | ROLE: Shared pytest fixtures & test helpers.                |
# | PLIK: tests/conftest.py                                     |
# | ROLA: Wspólne fikstury pytest i pomocniki testowe.          |
# +-------------------------------------------------------------+
"""
PL: Zbiór współdzielonych fikstur i pomocników testowych dla całego pakietu testów.
EN: Shared pytest fixtures and helpers used across the test suite.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
