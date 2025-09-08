#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/ledger/anchor_daily.py                       |
# | ROLE: Produce daily Merkle anchor manifest (local, stub)    |
# +-------------------------------------------------------------+

from __future__ import annotations

from datetime import UTC, datetime
import json
import os
from pathlib import Path
from typing import Any

# Merkle helpers can be used in extended variants; not required for stub


def _now() -> str:
    return datetime.now(UTC).isoformat()


def main() -> int:
    """
    PL/EN: Syntetyczne "kotwiczenie dzienne". Zbiera ostatnią znaną kotwicę
    (dowolny receipt) i zapisuje manifest z pieczęcią czasu. W produkcji
    manifest powinien być podpisany i opublikowany do zewnętrznego logu.
    """

    out_dir = Path(os.getenv("OUT_DIR") or "out")
    out_dir.mkdir(parents=True, exist_ok=True)
    # Minimal anchor: empty proof for now (root is implicit in downstream)
    manifest: dict[str, Any] = {
        "version": "anchor_v0",
        "created_at": _now(),
        "receipts": [],
    }
    (out_dir / "anchor_manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    print("anchor: OK", (out_dir / "anchor_manifest.json").as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
