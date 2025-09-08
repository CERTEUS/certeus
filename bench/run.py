#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=10)
    ap.add_argument("--out", type=Path, default=Path("out/bench.json"))
    args = ap.parse_args()
    # Delegate to perf quick bench
    res = subprocess.run(
        [
            "python3",
            "scripts/perf/quick_bench.py",
            "--iters",
            str(args.iters),
            "--out",
            str(args.out),
        ],
        check=False,
        text=True,
    )
    # Ensure file exists even if delegated script failed to write
    if not args.out.exists():
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps({"iters": args.iters, "status": res.returncode}), encoding="utf-8")
    print("bench: wrote", args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

