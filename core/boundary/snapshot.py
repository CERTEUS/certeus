#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/boundary/snapshot.py                           |
# | ROLE: Project module.                                       |
# | PLIK: core/boundary/snapshot.py                           |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Snapshot Boundary: liczy skróty per shardy na podstawie publicznych PCO
    i globalny digest. Uproszczone reguły: jeśli brak podkatalogów, traktuj
    katalog bazowy jako `shard-0`.

EN: Boundary snapshot: compute per-shard digests from public PCO bundles and
    a global digest. Simplified rule: if no subdirectories, treat the base
    directory as `shard-0`.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

# === MODELE / MODELS ===


@dataclass
class ShardStats:
    files: int
    bytes: int
    digest_hex: str


# === LOGIKA / LOGIC ===


def _iter_shards(base_dir: Path) -> dict[str, Path]:
    try:
        subs = [d for d in base_dir.iterdir() if d.is_dir()]
    except Exception:
        subs = []
    if not subs:
        return {"shard-0": base_dir}
    return {d.name: d for d in subs}


def _file_digest_hex(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as fh:
        for chunk in iter(lambda: fh.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def _shard_digest_from_leafs(leaf_hex_list: list[str]) -> str:
    # Deterministic: sort hex strings, then hash their ASCII concatenation
    concat = "".join(sorted(leaf_hex_list)).encode("ascii")
    return hashlib.sha256(concat).hexdigest()


def compute_shard_stats(dir_path: Path) -> ShardStats:
    files = 0
    total_bytes = 0
    leafs: list[str] = []

    for p in sorted(dir_path.rglob("*")):
        if p.is_file():
            files += 1
            try:
                size = p.stat().st_size
                total_bytes += int(size)
                leafs.append(_file_digest_hex(p))
            except Exception:
                # Defensive: ignore unreadable files but keep determinism
                leafs.append("0" * 64)

    digest_hex = _shard_digest_from_leafs(leafs)
    return ShardStats(files=files, bytes=total_bytes, digest_hex=digest_hex)


def _global_digest(shards: dict[str, ShardStats]) -> str:
    # Concatenate "shard-id:digest" in shard-id sorted order
    parts = [f"{sid}:{st.digest_hex}" for sid, st in sorted(shards.items())]
    return hashlib.sha256("".join(parts).encode("ascii")).hexdigest()


def compute_snapshot(base_dir: str | Path) -> dict[str, Any]:
    """
    PL/EN: Compute Boundary snapshot JSON structure.

    Returns a dict with keys: "shards", "global_digest".
    """
    base = Path(base_dir)
    shard_dirs = _iter_shards(base)
    shards_out: dict[str, Any] = {}

    stats: dict[str, ShardStats] = {}
    for shard_id, dir_path in shard_dirs.items():
        st = compute_shard_stats(dir_path)
        stats[shard_id] = st
        shards_out[shard_id] = {
            "files": st.files,
            "bytes": st.bytes,
            "digest": f"sha256:{st.digest_hex}",
        }

    ghex = _global_digest(stats)
    out = {
        "shards": shards_out,
        "global_digest": f"sha256:{ghex}",
    }
    return out


def dumps_snapshot(snapshot: dict[str, Any]) -> str:
    return json.dumps(snapshot, indent=2, sort_keys=True)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
