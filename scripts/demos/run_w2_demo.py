#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w2_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w2_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W2 — demo: Boundary recon + PNIP strict.

EN: W2 — demo: Boundary reconstruction + PNIP strict.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path, Path as _P
import sys as _sys

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def main() -> int:
    # Boundary: set isolated bundle dir (empty) to expect zeros
    tmp = Path("out/demo_w2_boundary")
    tmp.mkdir(parents=True, exist_ok=True)
    os.environ["PROOF_BUNDLE_DIR"] = str(tmp)

    c = TestClient(app)
    b1 = c.get("/v1/boundary/status").json()
    b2 = c.post("/v1/boundary/reconstruct").json()

    # PNIP strict: invalid hash should 400 with PNIP_INVALID
    os.environ["STRICT_PNIP"] = "1"
    r = c.post(
        "/v1/ledger/record-input",
        json={"case_id": "CASE-2", "document_hash": "sha1:bad"},
        headers={"X-Policy-Pack-ID": "WRONG", "X-Jurisdiction": "PL:lex"},
    )
    pnip_ok = (r.status_code == 400) and (
        r.json().get("detail", {}).get("error", {}).get("code") == "PNIP_INVALID"
    )

    # Quick perf bench (p95)
    import json as _json
    import subprocess

    p = subprocess.run(
        [
            "python",
            "scripts/perf/quick_bench.py",
            "--iters",
            "8",
            "--p95-max-ms",
            "300",
            "--out",
            "out/perf_bench.json",
        ],
        capture_output=True,
        text=True,
    )
    perf = {}
    try:
        perf = _json.loads(Path("out/perf_bench.json").read_text(encoding="utf-8"))
    except Exception:
        perf = {"error": "no-perf-report"}

    rep = {
        "boundary_status": b1,
        "boundary_reconstruct": b2,
        "pnip_strict_works": pnip_ok,
        "perf": {"rc": p.returncode, "worst_p95_ms": perf.get("worst_p95_ms")},
    }
    Path("reports").mkdir(parents=True, exist_ok=True)
    Path("reports/w2_demo.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {"ok": True, "delta_bits": b1.get("delta_bits", -1), "pnip_strict": pnip_ok}
        )
    )
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
