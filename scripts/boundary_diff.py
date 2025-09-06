#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/boundary_diff.py                            |
# | ROLE: Project script.                                       |
# | PLIK: scripts/boundary_diff.py                            |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Porównuje dwa snapshoty Boundary i wypisuje różnice (JSON na stdout).
EN: Compares two Boundary snapshots and prints differences (JSON to stdout).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def diff_snapshots(base: dict[str, Any], head: dict[str, Any]) -> dict[str, Any]:
    b_shards = (base.get("shards") or {}) if isinstance(base, dict) else {}
    h_shards = (head.get("shards") or {}) if isinstance(head, dict) else {}

    changed: list[str] = []
    details: dict[str, Any] = {}
    all_ids = sorted(set(b_shards.keys()) | set(h_shards.keys()))
    for sid in all_ids:
        b = b_shards.get(sid) or {}
        h = h_shards.get(sid) or {}
        if (
            (b.get("digest") != h.get("digest"))
            or (b.get("files") != h.get("files"))
            or (b.get("bytes") != h.get("bytes"))
        ):
            changed.append(sid)
            details[sid] = {"base": b, "head": h}

    status = "IDENTICAL" if not changed and (base.get("global_digest") == head.get("global_digest")) else "DIFFERENT"
    return {
        "status": status,
        "changed": changed,
        "global": {
            "base": base.get("global_digest"),
            "head": head.get("global_digest"),
        },
        "details": details,
    }


def main() -> int:
    sys.path.insert(0, str(_repo_root()))  # noqa: E402

    ap = argparse.ArgumentParser()
    ap.add_argument("base", help="Ścieżka do bazowego snapshotu JSON")
    ap.add_argument("head", help="Ścieżka do snapshotu HEAD JSON")
    args = ap.parse_args()

    base = json.loads(Path(args.base).read_text(encoding="utf-8"))
    head = json.loads(Path(args.head).read_text(encoding="utf-8"))

    out = diff_snapshots(base, head)
    print(json.dumps(out, indent=2))
    # Bezpiecznie zawsze 0; konsument może sprawdzić field "status"
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
