#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/p2p_smoke.py                          |
# | ROLE: Report-only smoke for SYNAPSY transport (stub)       |
# | PLIK: scripts/smokes/p2p_smoke.py                          |
# | ROLA: Smoke (raport) dla transportu SYNAPSY (stub)         |
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path

from runtime.p2p_transport import echo_roundtrip


def main() -> int:
    out = Path("out")
    out.mkdir(parents=True, exist_ok=True)
    rep = echo_roundtrip("hello-synapse")
    (out / "p2p_transport_smoke.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print("p2p transport smoke:", rep)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

