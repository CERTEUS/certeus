#!/usr/bin/env python3
# +=============================================================+
# |                      CERTEUS — GUARD                        |
# +=============================================================+
# | FILE: scripts/hooks/block_key_extensions.py                 |
# | ROLE: Block committing key material by extension.           |
# | NOTE: Used by pre-commit. Fails commit if any staged file   |
# |       matches forbidden extensions (pem,key,der,pfx,p12).   |
# +=============================================================+
from __future__ import annotations

import sys
from pathlib import Path

FORBIDDEN_EXT = {".pem", ".key", ".der", ".pfx", ".p12"}


def main(argv: list[str]) -> int:
    bad: list[str] = []
    for a in argv:
        p = Path(a)
        if p.suffix.lower() in FORBIDDEN_EXT:
            bad.append(str(p))
    if bad:
        print("⛔  BLOCKED: key material must not be committed:")
        for b in bad:
            print(f"   - {b}")
        print("\nHint: keep keys local; use env/JWKS or secrets manager instead.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
