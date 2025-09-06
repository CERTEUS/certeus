# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/compute_gauge_epsilon.py               |
# | ROLE: Project script.                                       |
# | PLIK: scripts/gates/compute_gauge_epsilon.py               |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Auto‑kalibracja progu ε dla Gauge‑Gate. Wyznacza epsilon na podstawie
    zmierzonych driftów holonomii (język/jurysdykcja/L↔T) i opcjonalnie
    telemetrii CFE (`/v1/cfe/curvature`).

EN: Auto‑calibration of epsilon for Gauge‑Gate. Derives epsilon from measured
    holonomy drifts (language/jurisdiction/L↔T) and optionally CFE telemetry
    (`/v1/cfe/curvature`).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any

# === LOGIKA / LOGIC ===


def _read_gauge_json(p: Path) -> float | None:
    try:
        if p.exists():
            data = json.loads(p.read_text(encoding="utf-8"))
            return float(((data or {}).get("gauge") or {}).get("holonomy_drift", 0.0))
    except Exception:
        return None
    return None


def _safe_import_components() -> dict[str, float]:
    comps: dict[str, float] = {}
    # Language holonomy (Ω‑Kernel)
    try:
        from core.omega_lang import holonomy_drift as _lang_hol

        samples = [
            {"text": "Publikuj dowód", "lang": "pl"},
            {"text": "Analizuj dowód", "lang": "pl"},
            {"text": "Podgląd dowód", "lang": "pl"},
        ]
        vals = [_lang_hol(s, cycle=("pl", "en")) for s in samples]
        comps["lang"] = float(sum(vals) / max(1, len(vals)))
    except Exception:
        pass
    # Jurisdiction holonomy (Ω‑Kernel)
    try:
        from core.omega_jurisdiction import holonomy_drift_jurisdiction as _jur_hol

        samples = [
            {"text": "ustawa rozporządzenie kodeks", "jurisdiction": "pl"},
            {"text": "Kodeks i ustawa", "jurisdiction": "pl"},
        ]
        vals = [_jur_hol(s, cycle=("pl", "eu")) for s in samples]
        comps["jurisdiction"] = float(sum(vals) / max(1, len(vals)))
    except Exception:
        pass
    # Litera↔Telos holonomy (Ω‑Kernel)
    try:
        from core.omega_litera_telos import holonomy_drift_lt as _lt_hol

        samples = [
            {"text": "literalnie przepis paragraf", "lt": "l"},
            {"text": "zakaz i wymóg", "lt": "l"},
        ]
        vals = [_lt_hol(s, cycle=("l", "t")) for s in samples]
        comps["litera_telos"] = float(sum(vals) / max(1, len(vals)))
    except Exception:
        pass

    # Optional: CFE curvature as upper bound suggestion
    base = os.getenv("CER_BASE")
    if base:
        try:
            import json as _json
            import urllib.request as _rq

            with _rq.urlopen(base.rstrip("/") + "/v1/cfe/curvature", timeout=3) as resp:
                data = _json.loads(resp.read().decode("utf-8"))
                comps["curvature_kappa_max"] = float(data.get("kappa_max", 0.0))
        except Exception:
            pass

    return comps


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", help="Opcjonalny plik metryk gauge.json (z compute_gauge_drift)")
    ap.add_argument("--out", required=True, help="Plik wynikowy JSON z epsilonem")
    ap.add_argument(
        "--margin",
        type=float,
        default=1e-6,
        help="Margines dodawany do max drift (domyślnie: 1e-6)",
    )
    args = ap.parse_args()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    # Seed from gauge drift file if provided
    seeds: list[float] = []
    if args.input:
        seed = _read_gauge_json(Path(args.input))
        if seed is not None:
            seeds.append(float(seed))

    comps = _safe_import_components()
    seeds.extend(float(v) for v in comps.values())
    max_drift = max(seeds) if seeds else 0.0
    eps = float(max_drift + float(args.margin))

    payload: dict[str, Any] = {
        "gauge": {
            "epsilon": eps,
            "max_drift": max_drift,
            "components": comps,
        }
    }
    out.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Computed epsilon={eps} (max_drift={max_drift})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
