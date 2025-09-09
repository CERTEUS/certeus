#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/security_bunker_gate.py                |
# | ROLE: Project gate script (TEE/Bunker + PQ-crypto note).    |
# | PLIK: scripts/gates/security_bunker_gate.py                |
# | ROLA: Skrypt bramki (TEE/Bunkier + noty PQ-crypto).         |
# +-------------------------------------------------------------+

"""
PL: Bramka bezpieczeństwa W9.
 - Jeśli `BUNKER=on|1|true` → wymagaj gotowości bunkra (attestation/flag),
   w przeciwnym razie FAIL.
 - PQ-crypto: placeholder — wypisuje status do podsumowania kroku,
   nie blokuje (WARN only).
 - Zmienne pomocnicze do testów/CI:
   - `BUNKER_ATTESTATION_PATH` — wymuś sprawdzanie jednego pliku JSON,
   - `BUNKER_MARKER_PATH` — alternatywny marker (istnienie pliku),
   - `BUNKER_FORCE_FAIL` — wymuś FAIL (diagnostycznie).

EN: Security gate W9.
 - If `BUNKER=on|1|true` → require bunker readiness (attestation/flag),
   otherwise FAIL.
 - PQ-crypto: placeholder — prints readiness in step summary (WARN only).
 - Helper env for tests/CI:
   - `BUNKER_ATTESTATION_PATH` — check only this JSON file,
   - `BUNKER_MARKER_PATH` — alternative marker (any existing file),
   - `BUNKER_FORCE_FAIL` — force FAIL (diagnostic).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path

# === LOGIKA / LOGIC ===


def _is_on(val: str | None) -> bool:
    return (val or "").strip().lower() in {"1", "true", "on", "yes"}


def _bunker_ready(repo_root: Path) -> bool:
    # Forced fail (diagnostic)
    if _is_on(os.getenv("BUNKER_FORCE_FAIL")):
        return False
    # Env flag takes precedence
    if _is_on(os.getenv("BUNKER_READY")):
        return True
    # Explicit overrides
    att_path = (os.getenv("BUNKER_ATTESTATION_PATH") or "").strip()
    if att_path:
        p = Path(att_path)
        if not p.exists():
            return False
        if p.suffix == ".json":
            try:
                obj = json.loads(p.read_text(encoding="utf-8"))
                # Optional RA verify (structure only)
                from security.ra import extract_fingerprint, verify_fingerprint

                fp_ok = verify_fingerprint(obj) or verify_fingerprint(extract_fingerprint(obj).to_dict())
                if not fp_ok:
                    # Not fatal unless explicitly required by TEE_RA_REQUIRE
                    if _is_on(os.getenv("TEE_RA_REQUIRE")):
                        return False
            except Exception:
                return False
        return True
    marker_path = (os.getenv("BUNKER_MARKER_PATH") or "").strip()
    if marker_path:
        return Path(marker_path).exists()
    # Default markers (any of)
    markers = [
        repo_root / "data" / "security" / "bunker.ready",
        repo_root / "security" / "bunker" / "attestation.json",
    ]
    for m in markers:
        try:
            if m.exists():
                if m.suffix == ".json":
                    json.loads(m.read_text(encoding="utf-8"))
                return True
        except Exception:
            continue
    return False


def _write_summary(text: str) -> None:
    p = os.getenv("GITHUB_STEP_SUMMARY")
    if not p:
        return
    try:
        with open(p, "a", encoding="utf-8") as f:
            f.write(text.rstrip() + "\n")
    except Exception:
        pass


def main() -> int:
    # Try to detect repo root from __file__ if available, otherwise use current directory
    try:
        repo = Path(__file__).resolve().parents[2]
    except NameError:
        repo = Path.cwd()

    bunker = _is_on(os.getenv("BUNKER") or os.getenv("PROOFGATE_BUNKER"))
    pq_ready = _is_on(os.getenv("PQCRYPTO_READY"))
    enforce_pq = _is_on(os.getenv("PQCRYPTO_REQUIRE") or os.getenv("SECURITY_ENFORCE")) or (
        (os.getenv("PROFILE") or os.getenv("ENV") or "").lower() in {"prod", "production"}
    )

    if not pq_ready:
        _write_summary("[PQ-crypto] readiness: NOT READY")
    else:
        _write_summary("[PQ-crypto] readiness: READY")
    if enforce_pq and not pq_ready:
        print("Security Bunker Gate (PQ): FAIL (require=1, not ready)")
        return 2

    if not bunker:
        print("Security Bunker Gate: OK (BUNKER=off)")
        return 0

    if _bunker_ready(repo):
        print("Security Bunker Gate: OK (BUNKER=on, attested)")
        return 0

    print("Security Bunker Gate: FAIL (BUNKER=on, not attested)")
    return 1


# === I/O / ENDPOINTS ===

if __name__ == "__main__":
    raise SystemExit(main())
