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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--flags", help="Ścieżka do pliku flag (opcjonalne)")
    ap.add_argument("--out", required=True, help="Ścieżka pliku wynikowego JSON")
    args = ap.parse_args()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    payload = {"gauge": {"holonomy_drift": 0.0, "compensators_count": 0}}
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
        # Prefer Ω‑Kernel holonomia językowa jeśli dostępna; fallback: CFE curvature (in-proc)
        try:
            from core.omega_lang import holonomy_drift  # type: ignore

            samples = [
                {"text": "Publikuj dowód", "lang": "pl"},
                {"text": "Analizuj dowód", "lang": "pl"},
                {"text": "Podgląd dowód", "lang": "pl"},
            ]
            drifts = [holonomy_drift(s, cycle=("pl", "en")) for s in samples]
            payload["gauge"]["holonomy_drift"] = float(sum(drifts) / max(1, len(drifts)))
        except Exception:
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

    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
