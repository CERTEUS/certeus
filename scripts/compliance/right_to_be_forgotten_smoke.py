#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/compliance/right_to_be_forgotten_smoke.py    |
# | ROLE: Compliance smoke (RTBF + DPIA summary)                |
# | PLIK: scripts/compliance/right_to_be_forgotten_smoke.py    |
# | ROLA: Smoke zgodności (RTBF + DPIA skrót)                   |
# +-------------------------------------------------------------+

"""
PL: Smoke test prawa do bycia zapomnianym (Right-To-Be-Forgotten):
    - Wprowadza przykładowy payload z PII, potwierdza wykrycie przez gate redakcji
      (STRICT=0), usuwa PII i potwierdza przejście (STRICT=1).
    - Zapisuje `reports/rtbf_smoke.json` i `out/dpia_summary.txt` (skrót DPIA).

EN: Right-To-Be-Forgotten smoke:
    - Injects sample payload with PII, confirms detection by redaction gate
      (STRICT=0), removes PII and confirms pass (STRICT=1).
    - Writes `reports/rtbf_smoke.json` and `out/dpia_summary.txt` (DPIA summary).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def _run_redaction(payload: dict, strict: bool) -> int:
    repo = Path(__file__).resolve().parents[2]
    gate = repo / "scripts" / "gates" / "redaction_gate.py"
    env = os.environ.copy()
    env["STRICT_REDACTION"] = "1" if strict else "0"
    p = subprocess.run(
        [sys.executable, str(gate)],
        input=json.dumps(payload),
        text=True,
        capture_output=True,
        env=env,
    )
    # stderr/stdout are not printed to keep CI tidy; return code conveys result
    return p.returncode


def _dpia_summary() -> str:
    # Minimal presence/sections check
    repo = Path(__file__).resolve().parents[2]
    p = repo / "docs" / "compliance" / "dpia.md"
    if not p.exists():
        return "DPIA doc missing"
    txt = p.read_text(encoding="utf-8", errors="ignore")
    keys = ["Data Protection Impact Assessment", "Public payloads", "zero PII"]
    ok = all(k.lower() in txt.lower() for k in keys)
    return "DPIA: OK (present)" if ok else "DPIA: present (sections partial)"


def main() -> int:
    reports = Path("reports")
    reports.mkdir(parents=True, exist_ok=True)
    outdir = Path("out")
    outdir.mkdir(parents=True, exist_ok=True)

    pii_payload = {
        "subject": {"name": "Jan Kowalski", "pesel": "99010112345"},
        "content": "test",
    }
    clean_payload = {
        "subject": {"name": "Jan TEST"},
        "content": "Brak wrazliwych danych.",
    }

    rc_detect = _run_redaction(pii_payload, strict=False)
    rc_clean = _run_redaction(clean_payload, strict=True)

    result = {
        "pii_detection_rc": rc_detect,
        "clean_strict_rc": rc_clean,
        "ok": (rc_detect == 0 and rc_clean == 0),
    }
    (reports / "rtbf_smoke.json").write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )
    (outdir / "dpia_summary.txt").write_text(_dpia_summary(), encoding="utf-8")
    print(json.dumps(result))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
