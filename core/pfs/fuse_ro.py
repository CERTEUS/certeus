#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/fuse_ro.py                                  |
# | ROLE: Read-only FUSE mount over ProofFS root (Linux)       |
# | PLIK: core/pfs/fuse_ro.py                                  |
# | ROLA: Montowanie RO FUSE nad korzeniem ProofFS (Linux)     |
# +-------------------------------------------------------------+

"""
PL: Prosty filesystem FUSE (read-only) mapujący drzewo ProofFS w user-space.
    Wymaga `fusepy` i dostępnego `/dev/fuse`. Używane testowo/DEV.

EN: Simple read-only FUSE filesystem mirroring ProofFS tree in user space.
    Requires `fusepy` and `/dev/fuse`. Intended for dev/tests.
"""

from __future__ import annotations

import os
from pathlib import Path
import stat
from typing import Any


def _fuse():  # lazy import; avoid hard dep in environments without fuse
    try:
        from fuse import FUSE, Operations  # type: ignore

        return FUSE, Operations
    except Exception as e:  # pragma: no cover
        raise ImportError("fusepy not available (pip install fusepy)") from e


class ROFS:  # minimal Operations subset
    def __init__(self, root: Path) -> None:
        self.root = root

    # Helper to map path
    def _p(self, path: str) -> Path:
        p = (self.root / path.lstrip("/")).resolve()
        if not str(p).startswith(str(self.root.resolve())):
            raise FileNotFoundError
        return p

    # getattr
    def getattr(self, path: str, fh: int | None = None) -> dict[str, Any]:  # type: ignore[override]
        p = self._p(path)
        st = os.lstat(p)
        mode = st.st_mode
        # force read-only mask
        mode &= ~stat.S_IWUSR & ~stat.S_IWGRP & ~stat.S_IWOTH
        return {
            "st_mode": mode,
            "st_ino": st.st_ino,
            "st_dev": st.st_dev,
            "st_nlink": st.st_nlink,
            "st_uid": st.st_uid,
            "st_gid": st.st_gid,
            "st_size": st.st_size,
            "st_atime": st.st_atime,
            "st_mtime": st.st_mtime,
            "st_ctime": st.st_ctime,
        }

    # readdir
    def readdir(self, path: str, fh: int):  # type: ignore[override]
        p = self._p(path)
        yield "."
        yield ".."
        if p.is_dir():
            yield from sorted(os.listdir(p))

    # open (read-only)
    def open(self, path: str, flags: int):  # type: ignore[override]
        if flags & (os.O_RDWR | os.O_WRONLY):
            raise PermissionError
        return os.open(self._p(path), os.O_RDONLY)

    def read(self, path: str, size: int, offset: int, fh: int):  # type: ignore[override]
        os.lseek(fh, offset, os.SEEK_SET)
        return os.read(fh, size)

    # prohibit writes
    def write(self, path: str, buf: bytes, offset: int, fh: int):  # type: ignore[override]
        raise PermissionError


def mount(root: Path, mount_point: Path, *, foreground: bool = False) -> None:
    FUSE, _Ops = _fuse()
    fs = ROFS(root)
    # allow_other may require fuse.conf; omit to be safe on CI
    FUSE(fs, str(mount_point), nothreads=True, foreground=foreground, ro=True)


__all__ = ["mount", "ROFS"]
