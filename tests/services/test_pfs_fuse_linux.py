#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_pfs_fuse_linux.py               |
# | ROLE: Linux-only smoke for FUSE mount (read-only)          |
# +-------------------------------------------------------------+

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
import subprocess
import pytest


linux_only = pytest.mark.skipif(sys.platform != "linux", reason="Linux-only FUSE smoke")


@linux_only
def test_fuse_mount_smoke() -> None:
    try:
        import fuse  # type: ignore  # noqa: F401
    except Exception:
        pytest.skip("fusepy not installed")
    if not Path("/dev/fuse").exists():
        pytest.skip("/dev/fuse not available on runner")

    root = Path("data/proof_fs").resolve()
    # Ensure there is at least a file to list
    sample_dir = root / "_smoke"
    sample_dir.mkdir(parents=True, exist_ok=True)
    sample_file = sample_dir / "hello.txt"
    sample_file.write_text("hello", encoding="utf-8")

    with tempfile.TemporaryDirectory() as d:
        mp = Path(d) / "mnt"
        mp.mkdir(parents=True, exist_ok=True)
        # Run mount in background
        proc = subprocess.Popen(
            [sys.executable, "scripts/pfs/fuse_mount.py", str(mp), "--root", str(root)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            # Give it a moment to mount
            import time

            time.sleep(1.0)
            # List mounted path
            listed = list((mp / "_smoke").glob("*.txt"))
            assert listed, "mounted directory listing is empty"
        finally:
            # Unmount via fusermount
            try:
                subprocess.run(["fusermount", "-u", str(mp)], check=False)
            except Exception:
                pass
            try:
                proc.terminate()
            except Exception:
                pass

