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
    ap.add_argument("--max-jaccard", type=float, default=None, help="Maksymalny jaccard_drift (omega)")
    ap.add_argument("--max-entropy", type=float, default=None, help="Maksymalny entropy_drift (omega)")
    ap.add_argument("--max-entity-jaccard", type=float, default=None, help="Maksymalny entity_jaccard_drift (omega)")
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

        # Prefer files; fallback to env text
        bef = _read_text(getattr(args, "before_file", None)) or os.getenv("OMEGA_BEFORE_TEXT", "")
        aft = _read_text(getattr(args, "after_file", None)) or os.getenv("OMEGA_AFTER_TEXT", "")
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
        # Optional thresholds (args/env); report-only unless ENFORCE_OMEGA_DRIFT=1
        fail = False
        thr_j = getattr(args, "max_jaccard", None)
        thr_e = getattr(args, "max_entropy", None)
        thr_n = getattr(args, "max_entity_jaccard", None)
        # env fallbacks
        if thr_j is None:
            try:
                thr_j = float(os.getenv("OMEGA_MAX_JACCARD", "")) if os.getenv("OMEGA_MAX_JACCARD") else None
            except Exception:
                thr_j = None
        if thr_e is None:
            try:
                thr_e = float(os.getenv("OMEGA_MAX_ENTROPY", "")) if os.getenv("OMEGA_MAX_ENTROPY") else None
            except Exception:
                thr_e = None
        if thr_n is None:
            try:
                thr_n = float(os.getenv("OMEGA_MAX_ENTITY_DRIFT", "")) if os.getenv("OMEGA_MAX_ENTITY_DRIFT") else None
            except Exception:
                thr_n = None
        if bef or aft:
            if thr_j is not None and payload["omega"]["jaccard_drift"] > thr_j:  # type: ignore[index]
                print(f"Omega Gate: jaccard_drift {payload['omega']['jaccard_drift']} > {thr_j} (threshold)")
                fail = True
            if thr_e is not None and payload["omega"]["entropy_drift"] > thr_e:  # type: ignore[index]
                print(f"Omega Gate: entropy_drift {payload['omega']['entropy_drift']} > {thr_e} (threshold)")
                fail = True
            if thr_n is not None and payload["omega"]["entity_jaccard_drift"] > thr_n:  # type: ignore[index]
                print(
                    f"Omega Gate: entity_jaccard_drift {payload['omega']['entity_jaccard_drift']} > {thr_n} (threshold)"
                )
                fail = True
        if fail and (os.getenv("ENFORCE_OMEGA_DRIFT") or "").strip() in {"1", "true", "True"}:
            out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
            return 1
    except Exception:
        # keep payload minimal if imports fail
        pass

    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
