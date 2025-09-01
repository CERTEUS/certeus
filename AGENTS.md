# CERTEUS — AGENTS.md (reguły dla agenta)

## Interpreter
Python: `.\.venv\Scripts\python.exe` (zmienna `$py`)

## Instalacja
`$py -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn`

## Środowisko
`./scripts/keys_dev.ps1`
`./scripts/env_load.ps1`

## Lint
`$py -m ruff check . --fix`
`$py -m ruff format .`

## Testy
`mkdir -Force reports`
`$py -m pytest -q --junitxml="reports\junit.xml"`

## Serwer
`$py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`

## Push
`git add -A`
`git commit -m "chore: lint+tests via Codex" --no-verify`
`git push -u origin HEAD:main`

## Premium Code Style (Sekcja 21 — rdzeń agenta)

- Standard: Każdy plik musi mieć baner CERTEUS na górze oraz docstring modułu PL/EN (patrz: `docs/manifest.md` — 21) Standard Kodowania).
- Sekcje w kodzie: agent utrzymuje znaczniki struktury pliku w Pythonie i skryptach: `# === IMPORTY / IMPORTS ===`, `# === KONFIGURACJA / CONFIGURATION ===`, `# === MODELE / MODELS ===`, `# === LOGIKA / LOGIC ===`, `# === I/O / ENDPOINTS ===`, `# === TESTY / TESTS ===`.
- Proof‑native: wejście PNIP i publikowalne wyjścia PCO są first‑class; nie logujemy sekretów; OTel w API (zob. 21.3–21.5).
- Linty/testy: ruff/pytest są bramką jakości; agent uruchamia `ruff check . --fix`, `ruff format .`, `pytest` przed push.
- Automatyzacja: w CI działa gate `scripts/check_premium_style.py` (wymusza banery/docstringi/sekcje). Workflow: `.github/workflows/ci-gates.yml`.
- Idempotencja: skrypty pomocnicze (apply_headers/apply_*_headers) mogą być uruchamiane wielokrotnie; nie duplikują nagłówków.
