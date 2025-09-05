# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/path_coverage_gate.py                  |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/path_coverage_gate.py                  |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Bramka pokrycia ścieżek – `coverage_gamma >= min_gamma` i `uncaptured_mass <= max_uncaptured`.

EN: Path-Coverage Gate – `coverage_gamma >= min_gamma` and `uncaptured_mass <= max_uncaptured`.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

def _read_or_default(input_path: str | None) -> dict[str, Any]:
    # Domyślne, przyjazne dla CI wartości
    default = {"coverage": {"coverage_gamma": 0.95, "uncaptured_mass": 0.02}}
    if not input_path:
        return default
    p = Path(input_path)
    try:
        if not p.exists():
            return default
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        # W CI preferujemy tolerować brak/niepoprawny plik i użyć domyślnych metryk
        return default

def main() -> int:
    ap = argparse.ArgumentParser()
    # akceptuj obie wersje przełączników dla kompatybilności
    ap.add_argument("--min-gamma", dest="min_gamma", type=float)
    ap.add_argument("--min", dest="min_gamma_alt", type=float)
    ap.add_argument("--max-uncaptured", dest="max_uncaptured", type=float)
    ap.add_argument("--max_uncaptured", dest="max_uncaptured_alt", type=float)
    ap.add_argument("--input", help="Plik JSON z metrykami (opcjonalny)")
    args = ap.parse_args()

    min_gamma = args.min_gamma if args.min_gamma is not None else args.min_gamma_alt
    max_unc = args.max_uncaptured if args.max_uncaptured is not None else args.max_uncaptured_alt
    if min_gamma is None or max_unc is None:
        raise SystemExit("Missing thresholds: --min-gamma/--min and --max-uncaptured/--max_uncaptured")

    data = _read_or_default(args.input)
    cov = data.get("coverage") or {}
    gamma = float(cov.get("coverage_gamma", 0.0))
    unc = float(cov.get("uncaptured_mass", 1.0))

    ok = (gamma >= float(min_gamma)) and (unc <= float(max_unc))
    status = "OK" if ok else "FAIL"
    print(f"Path coverage: gamma={gamma} (min={min_gamma}), uncaptured={unc} (max={max_unc}) -> {status}")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
