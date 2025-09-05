#!/usr/bin/env python3

"""
PL/EN: FUSE adapter stub — contract surface only; not used in CI directly.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class FuseMount:
    mount_path: Path
    ops: str = "ro"


def mount_readonly(root: Path) -> FuseMount:  # pragma: no cover - stub
    root.mkdir(parents=True, exist_ok=True)
    return FuseMount(mount_path=root)


def unmount(_m: FuseMount) -> None:  # pragma: no cover - stub
    return None

