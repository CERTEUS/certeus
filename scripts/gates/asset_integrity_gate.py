#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/asset_integrity_gate.py                |
# | ROLE: Verify basic integrity of public PCO assets            |
# | PLIK: scripts/gates/asset_integrity_gate.py                |
# | ROLA: Weryfikacja integralności publicznych artefaktów PCO   |
# +-------------------------------------------------------------+

"""
PL: Gate integralności zasobów (PCO). Sprawdza minimalną strukturę plików
    JSON w `data/public_pco/*.json`: obecność pól `spec`, `claims`, `proof.root`.
    Raport zapisuje do `out/asset_integrity.json`; tworzy `out/asset_ok.txt` przy OK.
    Egzekwowanie (exit 1) tylko, gdy `ASSET_INTEGRITY_ENFORCE=1`.

EN: Asset integrity gate. Verifies minimal structure of JSON PCO files under
    `data/public_pco/*.json`: requires `spec`, `claims`, `proof.root`. Writes
    `out/asset_integrity.json` and creates `out/asset_ok.txt` if all ok. Enforces
    failure only when `ASSET_INTEGRITY_ENFORCE=1`.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import glob
import json
import os
from pathlib import Path
from typing import Any


def _validate_pco(obj: dict[str, Any]) -> list[str]:
    missing: list[str] = []
    if "spec" not in obj:
        missing.append("spec")
    if "claims" not in obj or not isinstance(obj.get("claims"), list):
        missing.append("claims[]")
    proof = obj.get("proof") if isinstance(obj, dict) else None
    if not isinstance(proof, dict) or "root" not in proof:
        missing.append("proof.root")
    return missing


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)
    base = repo / "data" / "public_pco"
    files = sorted(glob.glob(str(base / "*.json"))) if base.exists() else []
    results: list[dict[str, Any]] = []
    ok_all = True
    for fp in files:
        try:
            obj = json.loads(Path(fp).read_text(encoding="utf-8"))
        except Exception as e:
            results.append({"file": fp, "error": str(e)})
            ok_all = False
            continue
        miss = _validate_pco(obj if isinstance(obj, dict) else {})
        results.append({"file": fp, "missing": miss})
        if miss:
            ok_all = False
    rep = {"checked": len(files), "ok": ok_all, "results": results}
    (out / "asset_integrity.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    if ok_all:
        (out / "asset_ok.txt").write_text("ok", encoding="utf-8")
        return 0
    if (os.getenv("ASSET_INTEGRITY_ENFORCE") or "0").strip() in {"1", "true", "True"}:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
