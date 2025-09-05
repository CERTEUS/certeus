#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/packs/update_abi_baselines.py               |
# | ROLE: Project script.                                       |
# | PLIK: scripts/packs/update_abi_baselines.py               |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Aktualizuje `plugins/*/abi_baseline.json` na podstawie bieżących modułów.

EN: Updates `plugins/*/abi_baseline.json` based on current modules.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

from dataclasses import asdict

# Ensure repo-root on sys.path for sibling imports (see AGENTS hub notes)
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))  # noqa: E402

from scripts.gates.pack_abi_semver_gate import _abi_for_module  # reuse


def _load_manifest(p: Path) -> dict[str, Any]:
    if yaml is not None:
        try:
            data = yaml.safe_load(p.read_text(encoding="utf-8"))
            return data or {}
        except Exception:
            return {}
    out: dict[str, Any] = {}
    for raw in p.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or ":" not in line:
            continue
        k, v = line.split(":", 1)
        out[k.strip()] = v.strip().strip("'\"")
    return out


def main() -> int:
    root = Path(".").resolve()
    plugdir = root / "plugins"
    if not plugdir.exists():
        print("No plugins/ directory; nothing to update")
        return 0
    updated = 0
    for man in plugdir.glob("*/plugin.yaml"):
        data = _load_manifest(man)
        name = str(data.get("name") or man.parent.name)
        mod = str(data.get("module") or "").strip()
        ver = str(data.get("version") or data.get("ver") or "").strip()
        desc = _abi_for_module(mod)
        d = {"__version__": ver}
        # dataclass with slots=True — use asdict instead of __dict__
        d.update(asdict(desc))
        outp = man.parent / "abi_baseline.json"
        outp.write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"Updated {outp} for {name} (version {ver})")
        updated += 1
    print(f"ABI baselines updated: {updated}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
