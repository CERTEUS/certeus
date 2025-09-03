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
PL: Bramka informacyjna PQ‑crypto. Jeśli PQCRYPTO_REQUIRE=1, wymaga READY
    przez PQCRYPTO_READY=1 lub pco.crypto.pq.ready (tu tylko raportujemy ENV).

EN: Informational PQ‑crypto gate. If PQCRYPTO_REQUIRE=1, expects READY via
    PQCRYPTO_READY=1 (we only report ENV here).
"""
from __future__ import annotations

import os
from pathlib import Path


def main() -> int:
    require = (os.getenv("PQCRYPTO_REQUIRE") or "").strip() in {"1", "true", "True"}
    ready = (os.getenv("PQCRYPTO_READY") or "").strip() in {"1", "true", "True"}
    status = "READY" if ready else ("REQUIRE" if require else "OFF")
    print(f"PQ-crypto gate: status={status} (ENV)")
    # Publish small marker used by PR comment builder
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)
    (out / "pqcrypto.txt").write_text(status, encoding="utf-8")
    # Never fail here (informational)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

