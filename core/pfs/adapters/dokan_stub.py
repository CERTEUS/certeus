#!/usr/bin/env python3

"""
PL/EN: Dokan (Windows) adapter stub — contract only; not used in CI.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class DokanMount:
    mount_path: Path
    ops: str = "ro"


def mount_readonly(root: Path) -> DokanMount:  # pragma: no cover - stub
    root.mkdir(parents=True, exist_ok=True)
    return DokanMount(mount_path=root)


def unmount(_m: DokanMount) -> None:  # pragma: no cover - stub
    return None
