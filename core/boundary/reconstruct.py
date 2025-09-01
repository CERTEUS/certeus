#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/boundary/reconstruct.py                        |
# | ROLE: Project module.                                       |
# | PLIK: core/boundary/reconstruct.py                        |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Rekonstrukcja Boundary (zbiorcza) na podstawie publicznych pakietów PCO.
    Zwraca `delta_bits` i mapę per-shard `bits_delta_map` (liczba niespójności).

EN: Boundary bulk reconstruction based on public PCO bundles. Returns
    `delta_bits` and per-shard `bits_delta_map` (count of inconsistencies).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from dataclasses import dataclass
import gzip
import hashlib
import json
from pathlib import Path
from typing import Any

from core.pco.crypto import canonical_bundle_hash_hex, compute_leaf_hex

# === KONFIGURACJA / CONFIGURATION ===


# === MODELE / MODELS ===
@dataclass
class MerkleStep:
    sibling: str
    dir: str  # "L" | "R"


# === LOGIKA / LOGIC ===


def _apply_merkle_path(leaf_hex: str, path: list[MerkleStep]) -> str:
    if not path:
        return leaf_hex.lower()
    cur = bytes.fromhex(leaf_hex)
    for step in path:
        sib = bytes.fromhex(step.sibling)
        if step.dir == "L":
            cur = hashlib.sha256(sib + cur).digest()
        elif step.dir == "R":
            cur = hashlib.sha256(cur + sib).digest()
        else:  # defensive
            raise ValueError(f"Invalid merkle step.dir: {step.dir}")
    return cur.hex()


def _parse_merkle_path(raw: object) -> list[MerkleStep]:
    if raw is None:
        return []
    # Allow either list[steps] or {path:[steps]}
    if isinstance(raw, dict) and "path" in raw:
        raw = raw["path"]
    out: list[MerkleStep] = []
    if isinstance(raw, list):
        for it in raw:
            if not isinstance(it, dict):
                raise ValueError("Invalid merkle step type")
            d = it.get("dir") or it.get("position")
            sib = it.get("sibling")
            if d not in ("L", "R"):
                raise ValueError("Invalid merkle step.dir/position")
            if not isinstance(sib, str) or not sib:
                raise ValueError("Invalid merkle step.sibling")
            out.append(MerkleStep(sibling=str(sib), dir=str(d)))
        return out
    raise ValueError("merkle_proof must be list or {path:[...]}")


def _iter_shards(base_dir: Path) -> dict[str, Path]:
    """
    EN/PL: Return mapping of shard-id -> directory. If no subdirs present,
    treat `base_dir` itself as `shard-0`.
    """
    shards: dict[str, Path] = {}
    try:
        subs = [d for d in base_dir.iterdir() if d.is_dir()]
    except Exception:
        subs = []
    if not subs:
        shards["shard-0"] = base_dir
        return shards
    for d in subs:
        shards[d.name] = d
    return shards


def _gzip_ratio(data: bytes) -> float:
    try:
        comp = gzip.compress(data)
        if len(data) == 0:
            return 1.0
        return max(0.0, min(1.0, len(comp) / len(data)))
    except Exception:
        return 1.0


def bulk_reconstruct(bundle_dir: str | Path) -> dict[str, Any]:
    """
    PL/EN: Iterate shards under `bundle_dir`, verify merkle roots of public PCO
    bundles. Count mismatches per shard as "bit deltas" surrogate.

    Returns:
      {
        "delta_bits": int,
        "bits_delta_map": {shard: int},
        "stats": {shard: {files, bytes, gzip_ratio}},
      }
    """
    base = Path(bundle_dir)
    shards = _iter_shards(base)
    bits_delta_map: dict[str, int] = {k: 0 for k in shards}
    stats: dict[str, dict[str, Any]] = {}

    for shard_id, dir_path in shards.items():
        mismatches = 0
        files = 0
        total_bytes = 0
        try:
            for p in sorted(dir_path.glob("*.json")):
                try:
                    raw = p.read_bytes()
                    total_bytes += len(raw)
                    files += 1
                    obj = json.loads(raw.decode("utf-8"))
                    rid = obj.get("rid") or obj.get("case_id")
                    smt2_hash = obj.get("smt2_hash")
                    lfsc = obj.get("lfsc")
                    drat = obj.get("drat") if isinstance(obj.get("drat"), str) else None
                    merkle_proof = obj.get("merkle_proof")
                    ledger = obj.get("ledger") or {}
                    mr_expected = None
                    if isinstance(ledger, dict):
                        mr_expected = ledger.get("merkle_root") or ledger.get("merkleRoot")

                    if not (isinstance(rid, str) and isinstance(smt2_hash, str) and isinstance(lfsc, str)):
                        mismatches += 1
                        continue

                    bundle_hash_hex = canonical_bundle_hash_hex(smt2_hash, lfsc, drat)
                    leaf_hex = compute_leaf_hex(rid, bundle_hash_hex)
                    try:
                        path = _parse_merkle_path(merkle_proof)
                        mr_computed = _apply_merkle_path(leaf_hex, path)
                    except Exception:
                        # unable to compute path => treat as mismatch
                        mismatches += 1
                        continue

                    if not isinstance(mr_expected, str) or mr_expected.lower() != mr_computed.lower():
                        mismatches += 1
                except Exception:
                    mismatches += 1
        except Exception:
            # shard unreadable => count as one mismatch sentinel
            mismatches += 1

        bits_delta_map[shard_id] = mismatches
        stats[shard_id] = {
            "files": files,
            "bytes": total_bytes,
            "gzip_ratio": _gzip_ratio(str(stats).encode("utf-8"))
            if files == 0
            else _gzip_ratio(b"0" * total_bytes // max(1, files)),
        }

    delta_bits = sum(bits_delta_map.values())
    return {"delta_bits": delta_bits, "bits_delta_map": bits_delta_map, "stats": stats}


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
