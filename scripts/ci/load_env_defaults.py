#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/ci/load_env_defaults.py                      |
# | ROLE: CI helper: load non-secret defaults to GITHUB_ENV      |
# | PLIK: scripts/ci/load_env_defaults.py                      |
# | ROLA: Pomocnik CI: załaduj domyślne wartości do GITHUB_ENV   |
# +-------------------------------------------------------------+

"""
PL: Ładuje domyślne wartości zmiennych (nie-sekrety) z pliku
`.github/certeus.env.defaults` i zapisuje je do `$GITHUB_ENV` tylko
jeśli nie są ustawione już w środowisku.

EN: Loads non-secret defaults from `.github/certeus.env.defaults` and
writes them to `$GITHUB_ENV` only if they are not already set.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import os
from pathlib import Path

# === LOGIKA / LOGIC ===
ALLOW = {
    "BUNKER",
    "PROOFGATE_BUNKER",
    "FINE_GRAINED_ROLES",
    "PQCRYPTO_REQUIRE",
    "PQCRYPTO_READY",
    "STRICT_DP_BUDGET",
}


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    defaults = repo / ".github" / "certeus.env.defaults"
    target = os.getenv("GITHUB_ENV")
    if not defaults.exists() or not target:
        return 0
    lines = defaults.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    for ln in lines:
        ln = ln.strip()
        if not ln or ln.startswith("#"):
            continue
        if "=" not in ln:
            continue
        k, v = ln.split("=", 1)
        k = k.strip()
        if k not in ALLOW:
            continue
        if os.getenv(k) is None or os.getenv(k) == "":
            out.append(f"{k}={v}")
    if out:
        with open(target, "a", encoding="utf-8") as fh:
            for line in out:
                fh.write(line + "\n")
    return 0


# === I/O / ENDPOINTS ===
if __name__ == "__main__":
    raise SystemExit(main())
