#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/pfs/fuse_mount.py                            |
# | ROLE: CLI — mount ProofFS root via FUSE (Linux)            |
# +-------------------------------------------------------------+

from __future__ import annotations

import argparse
import os
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser(description="Mount ProofFS root via FUSE (read-only)")
    ap.add_argument("mount_point", help="Mount point directory (will be created if missing)")
    ap.add_argument("--root", default=os.getenv("PROOFS_FS_ROOT") or "data/proof_fs", help="ProofFS root path")
    ap.add_argument("--foreground", action="store_true", help="Run in foreground")
    args = ap.parse_args()
    root = Path(args.root).resolve()
    mp = Path(args.mount_point).resolve()
    mp.mkdir(parents=True, exist_ok=True)
    from core.pfs.fuse_ro import mount

    mount(root, mp, foreground=bool(args.foreground))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
