# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/generate_openapi.py                           |
# | ROLE: Generate OpenAPI JSON to out/openapi.json             |
# | PLIK: scripts/generate_openapi.py                           |
# | ROLA: Wygeneruj OpenAPI JSON do out/openapi.json            |
# +-------------------------------------------------------------+

"""

PL: Skrypt pomocniczy do generowania OpenAPI (bez uruchamiania serwera).
    Zapisuje wynik do pliku `out/openapi.json`.

EN: Helper script to generate OpenAPI without starting the server.
    Writes result to `out/openapi.json`.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path
import sys

# Ensure repo root on sys.path for direct script execution
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))  # noqa: E402

from services.api_gateway.main import app  # noqa: E402

# === KONFIGURACJA / CONFIGURATION ===

OUT_DIR = REPO_ROOT / "out"
OUT_FILE = OUT_DIR / "openapi.json"

# === LOGIKA / LOGIC ===


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    spec = app.openapi()
    OUT_FILE.write_text(json.dumps(spec, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"OpenAPI written to {OUT_FILE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
