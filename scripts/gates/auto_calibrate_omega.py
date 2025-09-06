#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/auto_calibrate_omega.py               |
# | ROLE: Project script.                                       |
# | PLIK: scripts/gates/auto_calibrate_omega.py               |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Auto‑kalibracja progów Ω‑Kernel na podstawie par tekstów.
EN: Ω‑Kernel threshold auto‑calibration based on text pairs.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
from collections.abc import Iterable
import json
import math
from pathlib import Path
from statistics import mean

# === KONFIGURACJA / CONFIGURATION ===

PAIR_SEP = "|||"  # separator between before and after in pairs file


# === MODELE / MODELS ===


class _Metrics:
    def __init__(self) -> None:
        self.jaccard: list[float] = []
        self.entropy: list[float] = []
        self.entity: list[float] = []

    def add(self, j: float, e: float, n: float) -> None:
        self.jaccard.append(float(j))
        self.entropy.append(float(e))
        self.entity.append(float(n))


# === LOGIKA / LOGIC ===


def _read_pairs(path: Path) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if PAIR_SEP in line:
            b, a = line.split(PAIR_SEP, 1)
        elif "\t" in line:
            b, a = line.split("\t", 1)
        else:
            # if only one token, treat as identity pair
            b, a = line, line
        pairs.append((b.strip(), a.strip()))
    return pairs


def _quantile(values: list[float], q: float) -> float:
    if not values:
        return 0.0
    v = sorted(values)
    if q <= 0:
        return v[0]
    if q >= 1:
        return v[-1]
    pos = (len(v) - 1) * q
    lo = math.floor(pos)
    hi = math.ceil(pos)
    if lo == hi:
        return v[int(pos)]
    frac = pos - lo
    return v[lo] * (1 - frac) + v[hi] * frac


def _summarize(vals: list[float]) -> dict[str, float]:
    if not vals:
        return {"count": 0, "min": 0.0, "p50": 0.0, "p95": 0.0, "max": 0.0, "mean": 0.0}
    return {
        "count": float(len(vals)),
        "min": float(min(vals)),
        "p50": float(_quantile(vals, 0.5)),
        "p95": float(_quantile(vals, 0.95)),
        "max": float(max(vals)),
        "mean": float(mean(vals)),
    }


def calibrate(
    pairs: Iterable[tuple[str, str]], domain: str | None, q: float, margin: float
) -> dict:
    # late import for repo‑root path friendliness
    from pathlib import Path as _Path
    import sys as _sys

    _sys.path.insert(0, str(_Path(__file__).resolve().parents[2]))  # repo root
    from core.omega.transforms import (  # type: ignore
        apply_transform as _apply,
        compute_entity_drift as _entities,
        compute_entropy_drift as _entropy,
        compute_gauge_drift as _gauge,
    )

    raw = _Metrics()
    mapped = _Metrics()

    for before, after in pairs:
        gd = _gauge(before, after)
        ed = _entropy(before, after)
        nd = _entities(before, after)
        raw.add(gd.jaccard_drift, ed.entropy_drift, nd.entity_jaccard_drift)
        if domain:
            b2, _ = _apply(before, "domain_map", domain=domain)
            a2, _ = _apply(after, "domain_map", domain=domain)
            gd2 = _gauge(b2, a2)
            ed2 = _entropy(b2, a2)
            nd2 = _entities(b2, a2)
            mapped.add(gd2.jaccard_drift, ed2.entropy_drift, nd2.entity_jaccard_drift)

    def _rec(vals: _Metrics) -> dict[str, float]:
        return {
            "jaccard_max": (
                round(_quantile(vals.jaccard, q) * margin, 6) if vals.jaccard else 0.0
            ),
            "entropy_max": (
                round(_quantile(vals.entropy, q) * margin, 6) if vals.entropy else 0.0
            ),
            "entity_jaccard_max": (
                round(_quantile(vals.entity, q) * margin, 6) if vals.entity else 0.0
            ),
        }

    out: dict[str, object] = {
        "thresholds": {
            "omega": _rec(raw),
        },
        "stats": {
            "omega": {
                "jaccard": _summarize(raw.jaccard),
                "entropy": _summarize(raw.entropy),
                "entity": _summarize(raw.entity),
            }
        },
    }
    if domain:
        out["thresholds"]["omega_mapped"] = {**_rec(mapped), "domain": domain}  # type: ignore[index]
        out["stats"]["omega_mapped"] = {  # type: ignore[index]
            "jaccard": _summarize(mapped.jaccard),
            "entropy": _summarize(mapped.entropy),
            "entity": _summarize(mapped.entity),
        }
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--pairs",
        action="append",
        help="Plik par: 'before|||after' per linia (można powtarzać)",
    )
    ap.add_argument("--out", required=True, help="Ścieżka pliku wynikowego JSON")
    ap.add_argument("--domain", help="Opcjonalna domena: med|sec|code")
    ap.add_argument(
        "--percentile",
        type=float,
        default=0.95,
        help="Percentyl do rekomendacji progów (domyślnie 0.95)",
    )
    ap.add_argument(
        "--margin",
        type=float,
        default=1.0,
        help="Margines mnożnik do progów (domyślnie 1.0)",
    )
    args = ap.parse_args()

    pair_files: list[Path] = [Path(p) for p in (args.pairs or [])]
    if not pair_files:
        raise SystemExit("Brak plików --pairs; wskaż co najmniej jeden plik z parami")

    all_pairs: list[tuple[str, str]] = []
    for pf in pair_files:
        if not pf.exists():
            continue
        all_pairs.extend(_read_pairs(pf))

    if not all_pairs:
        data = calibrate([], args.domain, args.percentile, args.margin)
    else:
        data = calibrate(
            all_pairs,
            (args.domain or "").strip().lower() or None,
            args.percentile,
            args.margin,
        )

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
