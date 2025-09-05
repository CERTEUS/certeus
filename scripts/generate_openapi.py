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
DOCS_DIR = REPO_ROOT / "docs" / "openapi"

# === LOGIKA / LOGIC ===

def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    DOCS_DIR.mkdir(parents=True, exist_ok=True)
    spec = app.openapi()
    # D71: embed version/compat notes
    try:
        spec["info"]["version"] = spec.get("info", {}).get("version", "0.0.0")
        spec["info"]["x-compat"] = {
            "semver": "^1.0",
            "notes": "Backwards-compatible additions only; breaking changes require MAJOR bump.",
        }
    except Exception:
        pass
    # Save to out/openapi.json and docs/openapi/certeus.v1.json
    OUT_FILE.write_text(json.dumps(spec, ensure_ascii=False, indent=2), encoding="utf-8")
    (DOCS_DIR / "certeus.v1.json").write_text(json.dumps(spec, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"OpenAPI written to {OUT_FILE}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
