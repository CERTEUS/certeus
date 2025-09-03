#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/pqcrypto_gate.py                      |
# | ROLE: Project script.                                       |
# | PLIK: scripts/gates/pqcrypto_gate.py                      |
# | ROLA: Bramka informacyjna PQ-crypto (READY/REQUIRE).        |
# +-------------------------------------------------------------+
"""
PL: Bramka informacyjna PQ-crypto. Jeżeli PQCRYPTO_REQUIRE=1, wymaga READY
    przez PQCRYPTO_READY=1 lub pco.crypto.pq.ready (tu tylko raportujemy ENV).

EN: Informational PQ-crypto gate. If PQCRYPTO_REQUIRE=1, expects READY via
    PQCRYPTO_READY=1 (we only report ENV here).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os
from pathlib import Path

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def _is_on(v: str | None) -> bool:
    return (v or "").strip().lower() in {"1", "true", "on", "yes"}


def main() -> int:
    require = _is_on(os.getenv("PQCRYPTO_REQUIRE"))
    ready = _is_on(os.getenv("PQCRYPTO_READY"))
    status = "READY" if ready else ("REQUIRE" if require else "OFF")
    print(f"PQ-crypto gate: status={status} (ENV)")
    # Publish small marker used by PR comment builder
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)
    (out / "pqcrypto.txt").write_text(status, encoding="utf-8")
    # Never fail here (informational)
    return 0

# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())

# === TESTY / TESTS ===
