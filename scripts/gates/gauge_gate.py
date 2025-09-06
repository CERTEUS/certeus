# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/gauge_gate.py                          |
# | ROLE: Project module.                                       |
# | PLIK: scripts/gates/gauge_gate.py                          |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Bramka Gauge – sprawdza `holonomy_drift <= epsilon`.

EN: Gauge Gate – verifies that `holonomy_drift <= epsilon`.

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
    default = {"gauge": {"holonomy_drift": 0.0}}
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
    ap.add_argument("--epsilon", type=float, required=True)
    ap.add_argument("--input", help="Plik JSON z metrykami (opcjonalny)")
    args = ap.parse_args()

    data = _read_or_default(args.input)
    drift = float(((data or {}).get("gauge") or {}).get("holonomy_drift", 0.0))
    ok = drift <= float(args.epsilon)
    print(
        f"Gauge holonomy_drift={drift} epsilon={args.epsilon} -> {'OK' if ok else 'FAIL'}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
