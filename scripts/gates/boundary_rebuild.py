# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/boundary_rebuild.py                    |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/boundary_rebuild.py                    |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Alias uruchamiający bramkę Boundary (kompatybilność z dokumentacją).

EN: Compatibility alias to run Boundary gate.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import sys

from scripts.gates.boundary_rebuild_gate import main as _gate_main

if __name__ == "__main__":
    sys.exit(_gate_main())
