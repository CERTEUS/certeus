#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/pqcrypto_gate.py                      |
# | ROLE: Gate: PQ-crypto readiness (stub/require)              |
# | PLIK: scripts/gates/pqcrypto_gate.py                      |
# | ROLA: Bramka: gotowość PQ-crypto (stub/wymagaj)             |
# +-------------------------------------------------------------+

"""
PL: Bramka gotowości PQ-crypto. Jeśli `PQCRYPTO_REQUIRE=1`, wymaga
   `PQCRYPTO_READY=1` (lub heurystyki modułów) i zwraca FAIL jeśli brak.

EN: PQ-crypto readiness gate. If `PQCRYPTO_REQUIRE=1`, requires
   `PQCRYPTO_READY=1` (or minimal module heuristics) else FAIL.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os

# === LOGIKA / LOGIC ===

def _is_on(v: str | None) -> bool:
    return (v or "").strip().lower() in {"1", "true", "on", "yes"}

def main() -> int:
    require = _is_on(os.getenv("PQCRYPTO_REQUIRE"))
    ready = _is_on(os.getenv("PQCRYPTO_READY"))

    if not require:
        print("PQ-crypto Gate: OK (require=off)")
        return 0

    if ready:
        print("PQ-crypto Gate: OK (ready)")
        return 0

    print("PQ-crypto Gate: FAIL (require=on, not ready)")
    return 1

# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
