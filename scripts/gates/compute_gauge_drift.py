# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/compute_gauge_drift.py                 |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/compute_gauge_drift.py                 |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Stub obliczenia holonomii sensu (Gauge). Zapisuje JSON z metrykami.

EN: Gauge holonomy stub computation. Writes out a JSON with metrics.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import json
import json as _json
import os
from pathlib import Path
import urllib.request

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def _read_text(p: str | None) -> str:
    if not p:
        return ""
    try:
        return Path(p).read_text(encoding="utf-8")
    except Exception:
        return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--flags", help="Ścieżka do pliku flag (opcjonalne)")
    ap.add_argument("--out", required=True, help="Ścieżka pliku wynikowego JSON")
    ap.add_argument("--before-file", help="Opcjonalny plik 'before' do obliczeń Ω‑Kernel drift")
    ap.add_argument("--after-file", help="Opcjonalny plik 'after' do obliczeń Ω‑Kernel drift")
    args = ap.parse_args()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    payload: dict[str, object] = {"gauge": {"holonomy_drift": 0.0, "compensators_count": 0}}
    # Optional: real telemetry from running API if CER_BASE provided
    base = os.getenv("CER_BASE")
    if base:
        try:
            with urllib.request.urlopen(base.rstrip("/") + "/v1/cfe/curvature", timeout=3) as resp:
                data = _json.loads(resp.read().decode("utf-8"))
                kappa = float(data.get("kappa_max", 0.0))
                payload["gauge"]["holonomy_drift"] = kappa
        except Exception:
            pass
    else:
        # In-proc fallback: import FastAPI app and query via TestClient (requires fastapi installed)
        try:
            from fastapi.testclient import TestClient  # type: ignore

            from services.api_gateway.main import app  # type: ignore

            with TestClient(app) as client:  # type: ignore
                r = client.get("/v1/cfe/curvature")
                if r.status_code == 200:
                    data = r.json()
                    kappa = float(data.get("kappa_max", 0.0))
                    payload["gauge"]["holonomy_drift"] = kappa
        except Exception:
            pass

    # Ω‑Kernel drift (report‑only): use optional before/after files
    try:
        import sys as _sys

        _sys.path.insert(0, str(Path(__file__).resolve().parents[2]))  # repo‑root
        from core.omega.transforms import (
            compute_entity_drift as _entities,
            compute_entropy_drift as _entropy,
            compute_gauge_drift as _gauge,
        )

        bef = _read_text(getattr(args, "before_file", None))
        aft = _read_text(getattr(args, "after_file", None))
        if bef or aft:
            gd = _gauge(bef, aft)
            ed = _entropy(bef, aft)
            nd = _entities(bef, aft)
            payload["omega"] = {
                "token_count_delta": gd.token_count_delta,
                "jaccard_drift": gd.jaccard_drift,
                "entropy_drift": ed.entropy_drift,
                "entity_jaccard_drift": nd.entity_jaccard_drift,
            }
        else:
            payload["omega"] = {
                "token_count_delta": 0,
                "jaccard_drift": 0.0,
                "entropy_drift": 0.0,
                "entity_jaccard_drift": 0.0,
            }
    except Exception:
        # keep payload minimal if imports fail
        pass

    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
