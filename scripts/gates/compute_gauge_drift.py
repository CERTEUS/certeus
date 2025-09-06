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
    Obsługa trybu domenowego (MED/SEC/CODE) z `domain_map` (raport‑only).

EN: Gauge holonomy stub computation. Writes out a JSON with metrics.
    Supports domain mode (MED/SEC/CODE) via `domain_map` (report‑only).

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
    ap.add_argument(
        "--before-file", help="Opcjonalny plik 'before' do obliczeń Ω‑Kernel drift"
    )
    ap.add_argument(
        "--after-file", help="Opcjonalny plik 'after' do obliczeń Ω‑Kernel drift"
    )
    ap.add_argument(
        "--max-jaccard",
        type=float,
        default=None,
        help="Maksymalny jaccard_drift (omega)",
    )
    ap.add_argument(
        "--max-entropy",
        type=float,
        default=None,
        help="Maksymalny entropy_drift (omega)",
    )
    ap.add_argument(
        "--max-entity-jaccard",
        type=float,
        default=None,
        help="Maksymalny entity_jaccard_drift (omega)",
    )
    ap.add_argument(
        "--domain", help="Opcjonalna domena dla domain_map: med|sec|code (raport‑only)"
    )
    ap.add_argument(
        "--max-jaccard-mapped",
        type=float,
        default=None,
        help="Maksymalny jaccard_drift (omega_mapped)",
    )
    ap.add_argument(
        "--max-entropy-mapped",
        type=float,
        default=None,
        help="Maksymalny entropy_drift (omega_mapped)",
    )
    ap.add_argument(
        "--max-entity-jaccard-mapped",
        type=float,
        default=None,
        help="Maksymalny entity_jaccard_drift (omega_mapped)",
    )
    args = ap.parse_args()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    payload: dict[str, object] = {
        "gauge": {"holonomy_drift": 0.0, "compensators_count": 0}
    }
    # Optional: real telemetry from running API if CER_BASE provided
    base = os.getenv("CER_BASE")
    if base:
        try:
            with urllib.request.urlopen(
                base.rstrip("/") + "/v1/cfe/curvature", timeout=3
            ) as resp:
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
            payload["gauge"]["holonomy_drift"] = float(
                sum(drifts) / max(1, len(drifts))
            )
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

    # Ω‑Kernel drift (report‑only): use optional before/after files
    try:
        import sys as _sys

        _sys.path.insert(0, str(Path(__file__).resolve().parents[2]))  # repo‑root
        from core.omega.transforms import (
            apply_transform as _apply,
            compute_entity_drift as _entities,
            compute_entropy_drift as _entropy,
            compute_gauge_drift as _gauge,
        )

        # Prefer files; fallback to env text
        bef = _read_text(getattr(args, "before_file", None)) or os.getenv(
            "OMEGA_BEFORE_TEXT", ""
        )
        aft = _read_text(getattr(args, "after_file", None)) or os.getenv(
            "OMEGA_AFTER_TEXT", ""
        )
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
            # Optional domain mapping (report-only): compute metrics after domain_map
            dom = (
                (getattr(args, "domain", None) or os.getenv("OMEGA_DOMAIN") or "")
                .strip()
                .lower()
            )
            if dom in {"med", "sec", "code"}:
                bef_m, _ = _apply(bef, "domain_map", domain=dom)
                aft_m, _ = _apply(aft, "domain_map", domain=dom)
                gd2 = _gauge(bef_m, aft_m)
                ed2 = _entropy(bef_m, aft_m)
                nd2 = _entities(bef_m, aft_m)
                payload["omega_mapped"] = {
                    "domain": dom,
                    "token_count_delta": gd2.token_count_delta,
                    "jaccard_drift": gd2.jaccard_drift,
                    "entropy_drift": ed2.entropy_drift,
                    "entity_jaccard_drift": nd2.entity_jaccard_drift,
                }
                # Optional thresholds for mapped metrics (report-only by default)
                fail_mapped = False
                thr_j2 = getattr(args, "max_jaccard_mapped", None)
                thr_e2 = getattr(args, "max_entropy_mapped", None)
                thr_n2 = getattr(args, "max_entity_jaccard_mapped", None)
                # env fallbacks
                import os as _os

                if thr_j2 is None:
                    try:
                        thr_j2 = (
                            float(_os.getenv("OMEGA_MAX_JACCARD_MAPPED", ""))
                            if _os.getenv("OMEGA_MAX_JACCARD_MAPPED")
                            else None
                        )
                    except Exception:
                        thr_j2 = None
                if thr_e2 is None:
                    try:
                        thr_e2 = (
                            float(_os.getenv("OMEGA_MAX_ENTROPY_MAPPED", ""))
                            if _os.getenv("OMEGA_MAX_ENTROPY_MAPPED")
                            else None
                        )
                    except Exception:
                        thr_e2 = None
                if thr_n2 is None:
                    try:
                        thr_n2 = (
                            float(_os.getenv("OMEGA_MAX_ENTITY_DRIFT_MAPPED", ""))
                            if _os.getenv("OMEGA_MAX_ENTITY_DRIFT_MAPPED")
                            else None
                        )
                    except Exception:
                        thr_n2 = None
                if thr_j2 is not None and payload["omega_mapped"]["jaccard_drift"] > thr_j2:  # type: ignore[index]
                    jd = payload["omega_mapped"]["jaccard_drift"]  # type: ignore[index]
                    print(
                        f"Omega Mapped Gate: jaccard_drift {jd} > {thr_j2} (threshold)"
                    )
                    fail_mapped = True
                if thr_e2 is not None and payload["omega_mapped"]["entropy_drift"] > thr_e2:  # type: ignore[index]
                    edv = payload["omega_mapped"]["entropy_drift"]  # type: ignore[index]
                    print(
                        f"Omega Mapped Gate: entropy_drift {edv} > {thr_e2} (threshold)"
                    )
                    fail_mapped = True
                if thr_n2 is not None and payload["omega_mapped"]["entity_jaccard_drift"] > thr_n2:  # type: ignore[index]
                    print(
                        "Omega Mapped Gate: entity_jaccard_drift "
                        f"{payload['omega_mapped']['entity_jaccard_drift']} > {thr_n2} (threshold)"
                    )
                    fail_mapped = True
                # Only enforce fail if explicit opt-in
                if fail_mapped and (
                    _os.getenv("ENFORCE_OMEGA_MAPPED") or ""
                ).strip() in {"1", "true", "True"}:
                    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
                    return 1
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
                thr_j = (
                    float(os.getenv("OMEGA_MAX_JACCARD", ""))
                    if os.getenv("OMEGA_MAX_JACCARD")
                    else None
                )
            except Exception:
                thr_j = None
        if thr_e is None:
            try:
                thr_e = (
                    float(os.getenv("OMEGA_MAX_ENTROPY", ""))
                    if os.getenv("OMEGA_MAX_ENTROPY")
                    else None
                )
            except Exception:
                thr_e = None
        if thr_n is None:
            try:
                thr_n = (
                    float(os.getenv("OMEGA_MAX_ENTITY_DRIFT", ""))
                    if os.getenv("OMEGA_MAX_ENTITY_DRIFT")
                    else None
                )
            except Exception:
                thr_n = None
        if bef or aft:
            if thr_j is not None and payload["omega"]["jaccard_drift"] > thr_j:  # type: ignore[index]
                print(
                    f"Omega Gate: jaccard_drift {payload['omega']['jaccard_drift']} > {thr_j} (threshold)"
                )
                fail = True
            if thr_e is not None and payload["omega"]["entropy_drift"] > thr_e:  # type: ignore[index]
                print(
                    f"Omega Gate: entropy_drift {payload['omega']['entropy_drift']} > {thr_e} (threshold)"
                )
                fail = True
            if thr_n is not None and payload["omega"]["entity_jaccard_drift"] > thr_n:  # type: ignore[index]
                print(
                    f"Omega Gate: entity_jaccard_drift {payload['omega']['entity_jaccard_drift']} > {thr_n} (threshold)"
                )
                fail = True
        if fail and (os.getenv("ENFORCE_OMEGA_DRIFT") or "").strip() in {
            "1",
            "true",
            "True",
        }:
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
