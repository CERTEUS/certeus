# +-------------------------------------------------------------+
# |                 CERTEUS - smoke286 helper                   |
# +-------------------------------------------------------------+
# | FILE: scripts/smoke286.ps1                                  |
# | ROLE: One-liner to run build->smoke->tests                  |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

param()

uv run python scripts/lexlog_eval_smoke_fallback.py
uv run pytest -q tests/services/test_lexlog_parser.py
