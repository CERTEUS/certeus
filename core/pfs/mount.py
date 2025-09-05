#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/mount.py                                    |
# | ROLE: Mock mount/unmount API (contract only)               |
# | PLIK: core/pfs/mount.py                                    |
# | ROLA: Mock API montowania/odmontowania (kontrakt)          |
# +-------------------------------------------------------------+

"""
PL: Mock API dla ProofFS mount/unmount kompatybilne z Linux/macOS (FUSE)
    i Windows (Dokan). Żadnych driverów nie instalujemy w CI — to tylko
    interfejs i rejestr w pamięci do testów E2E i inspekcji UI.

EN: Mock mount/unmount API compatible with Linux/macOS (FUSE) and Windows
    (Dokan). No kernel drivers in CI — contract + in‑memory registry only.
"""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path

_REGISTRY: dict[str, Path] = {}


@dataclass(frozen=True)
class MountInfo:
    mount_id: str
    mount_path: Path


def mount_readonly(source_root: str | os.PathLike[str] | None = None) -> MountInfo:
    """
    PL/EN: Register a mock mount. Returns MountInfo with mount_id and path.
    The mount point is the source_root path (no actual FS mount performed).
    """
    src = Path(source_root or os.getenv("PROOFS_FS_ROOT") or "data/proof_fs").resolve()
    src.mkdir(parents=True, exist_ok=True)
    mid = f"mock-{os.getpid()}-{len(_REGISTRY) + 1}"
    _REGISTRY[mid] = src
    return MountInfo(mount_id=mid, mount_path=src)


def unmount(mount_id: str) -> bool:
    """
    PL/EN: Unregister a mock mount by id. Returns True if removed.
    """
    return _REGISTRY.pop(mount_id, None) is not None


def get_mount_path(mount_id: str) -> Path | None:
    return _REGISTRY.get(mount_id)
