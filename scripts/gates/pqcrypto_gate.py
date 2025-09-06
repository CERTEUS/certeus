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
    (wykrywane automatycznie przez pyoqs/ML‑DSA lub ENV `PQCRYPTO_READY=1`).

EN: Informational PQ-crypto gate. If PQCRYPTO_REQUIRE=1, expects READY
    (auto-detected via pyoqs/ML‑DSA or ENV `PQCRYPTO_READY=1`).
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


def _detect_pq_ready() -> bool:
    # Try pyoqs ML‑DSA (Dilithium) sign/verify
    try:
        from security import pq_mldsa as pq

        kp = pq.generate_keypair()
        msg = b"certeus-pq-selftest"
        sig = pq.sign(msg, kp.secret_key)
        ok = pq.verify(msg, sig, kp.public_key)
        return bool(ok)
    except Exception:
        return False


def main() -> int:
    require = _is_on(os.getenv("PQCRYPTO_REQUIRE"))
    ready_env = _is_on(os.getenv("PQCRYPTO_READY"))
    ready_auto = _detect_pq_ready()
    ready = ready_env or ready_auto
    status = "READY" if ready else ("REQUIRE" if require else "OFF")
    print(f"PQ-crypto gate: status={status} (auto={ready_auto} env={ready_env})")
    # Publish small marker used by PR comment builder
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)
    (out / "pqcrypto.txt").write_text(status, encoding="utf-8")
    # Enforce if required
    if require and not ready:
        print("PQ-crypto gate: FAIL (require=1, not ready)")
        return 2
    return 0


# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())

# === TESTY / TESTS ===
