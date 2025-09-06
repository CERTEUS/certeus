#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/supply_chain/generate_sbom.py                |
# | ROLE: Project script.                                       |
# | PLIK: scripts/supply_chain/generate_sbom.py                |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: Generuje lekki SBOM (stub) dla lokalnego repo — lista plików + sha256,
    zapis do reports/sbom.json. Użyteczne do lokalnego audytu w W2.

EN: Generates a lightweight SBOM (stub) for the local repo — file list + sha256,
    written to reports/sbom.json. Useful for local audit in W2.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_hex(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    root = Path.cwd()
    include = ["services", "core", "scripts", "clients/web/public", "policies"]
    files: list[dict[str, Any]] = []
    for pat in include:
        d = root / pat
        if not d.exists():
            continue
        for p in d.rglob("*"):
            if not p.is_file():
                continue
            try:
                hx = _sha256_hex(p)
                files.append(
                    {
                        "path": str(p.relative_to(root)),
                        "sha256": hx,
                        "size": p.stat().st_size,
                    }
                )
            except Exception:
                continue
    sbom = {
        "schema": "certeus-sbom-v0.1",
        "root": str(root.name),
        "files": files,
    }
    out = Path("reports")
    out.mkdir(parents=True, exist_ok=True)
    (out / "sbom.json").write_text(json.dumps(sbom, indent=2), encoding="utf-8")
    print(json.dumps({"ok": True, "files": len(files)}))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
