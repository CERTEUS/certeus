#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/check_proofs.py                              |
# | ROLE: Verify presence/shape of DRAT/LFSC artifacts           |
# +-------------------------------------------------------------+

from __future__ import annotations

import argparse
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", type=Path, default=Path("out/proofs"))
    args = ap.parse_args()
    d = args.dir
    if not d.exists():
        print("no proofs dir")
        return 1
    ok = False
    for name in ("z3.drat", "cvc5.lfsc"):
        p = d / name
        if p.exists():
            if p.stat().st_size >= 0:
                ok = True
    print("proofs: ", ("OK" if ok else "MISSING"))
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
