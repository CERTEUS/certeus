#!/usr/bin/env python3
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | MODULE / MODUŁ: core/pco/merkle.py                                  |
# | DATE / DATA: 2025-08-19                                             |
# +=====================================================================+
# | EN: Merkle step type, proof parsing (MVP / legacy), and root apply. |
# | PL: Typ kroku Merkle, parser dowodu (MVP/legacy) i obliczanie korza.|
# +=====================================================================+

from __future__ import annotations

# ----Bloki----- IMPORTY
import hashlib
from dataclasses import dataclass
from typing import Any, Literal

# ----Bloki----- TYPY
Dir = Literal["L", "R"]


@dataclass(frozen=True, slots=True)
class MerkleStep:
    sibling: str  # hex
    dir: Dir  # "L" | "R"


# ----Bloki----- HASH
def _h(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()


# ----Bloki----- MERKLE
def parse_merkle_proof(raw: Any) -> list[MerkleStep]:
    """
    EN/PL: Accept:
      • [] (MVP)
      • [{"sibling":HEX, "dir":"L|R"}]
      • {"path":[.]} legacy; alias 'position' ≡ 'dir'
    """
    if raw is None:
        return []
    if isinstance(raw, dict) and "path" in raw:
        raw = raw["path"]
    if isinstance(raw, list):
        out: list[MerkleStep] = []
        for step in raw:
            if isinstance(step, MerkleStep):
                out.append(step)
                continue
            if not isinstance(step, dict):
                raise ValueError("Invalid merkle step: must be object")
            d = step.get("dir") or step.get("position")
            sib = step.get("sibling")
            if d not in ("L", "R") or not isinstance(sib, str) or not sib:
                raise ValueError("Invalid merkle step fields")
            out.append(MerkleStep(sibling=sib, dir=d))  # type: ignore[arg-type]
        return out
    raise ValueError("merkle_proof must be list or {path:[.]}")


def apply_merkle_path(leaf_hex: str, path: list[MerkleStep]) -> str:
    cur = bytes.fromhex(leaf_hex)
    for step in path:
        sib = bytes.fromhex(step.sibling)
        if step.dir == "L":
            cur = _h(sib + cur)
        else:  # "R"
            cur = _h(cur + sib)
    return cur.hex()
