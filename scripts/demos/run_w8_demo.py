#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w8_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w8_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W8 — LEXENITH v0.1 demo: Motion generator → CLDF renormalize → Why‑Not export →
    Micro‑Court lock→publish oraz DR lock/revoke.

EN: W8 — LEXENITH v0.1 demo: Motion generator → CLDF renormalize → Why‑Not export →
    Micro‑Court lock→publish and DR lock/revoke.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    c = TestClient(app)
    case = "LEX-W8-001"

    # 1) Motion generator with citations
    cites = ["Art. 5 k.c.", "III 2020"]
    mot = c.post(
        "/v1/lexenith/motion/generate",
        json={
            "case_id": case,
            "pattern_id": "motion-dismiss",
            "facts": {"A": 1},
            "citations": cites,
        },
    ).json()

    # 2) CLDF renormalize
    cldf_in = [{"text": x, "weight": 1.0 if i == 0 else 0.5} for i, x in enumerate(cites)]
    cldf = c.post("/v1/lexenith/cldf/renormalize", json={"citations": cldf_in}).json()

    # 3) Why‑Not export
    wn = c.post(
        "/v1/lexenith/why_not/export",
        json={
            "claim": "Powództwo o zapłatę",
            "counter_arguments": ["brak legitymacji", "nadmierne roszczenie"],
        },
    ).json()

    # 4) Micro‑Court lock → publish
    lock = c.post("/v1/lexenith/micro_court/lock", json={"case_id": case}).json()
    pub = c.post(
        "/v1/lexenith/micro_court/publish",
        json={"case_id": case, "footnotes": ["Hash this footnote"]},
    ).json()

    # 5) DR lock/revoke (horyzont w sprawach)
    dr_lock = c.post("/v1/dr/lock", json={"case": case, "reason": "court-hold"}).json()
    dr_revoke = c.post("/v1/dr/revoke", json={"lock_ref": dr_lock.get("lock_ref", "lock://unknown/")}).json()

    rep = {
        "case": case,
        "motion": mot,
        "cldf": cldf,
        "why_not": wn,
        "micro_court": {"lock": lock, "publish": pub},
        "dr": {"lock": dr_lock, "revoke": dr_revoke},
    }
    Path("reports").mkdir(parents=True, exist_ok=True)
    Path("reports/w8_demo.json").write_text(json.dumps(rep, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({"ok": True, "case": case}))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
