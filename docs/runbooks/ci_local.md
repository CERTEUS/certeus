# CI – lokalny runbook (lint, testy, środowisko)

Krótki przewodnik jak lokalnie uruchomić podstawowe kroki CI: środowisko, lint, testy i szybkie smoki. Zachowujemy zgodność z procedurą z `AGENTS.md`.

## Środowisko

- Python 3.11 (zalecany)
- Wirtualne środowisko w repo: `.venv`
- Skrypty pomocnicze kluczy/ENV (Windows): `./scripts/keys_dev.ps1`, `./scripts/env_load.ps1`

Linux/macOS:

```
python -m venv .venv && source .venv/bin/activate
python -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn
```

Windows (PowerShell):

```
py -3.11 -m venv .venv; .\.venv\Scripts\Activate.ps1
$py = ".\\.venv\\Scripts\\python.exe"
& $py -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn
```

Opcjonalnie załaduj lokalne klucze/ENV (Windows):

```
./scripts/keys_dev.ps1
./scripts/env_load.ps1
```

## Lint (ruff)

```
python -m ruff check . --fix
python -m ruff format .
```

## Testy (pytest)

Szybki bieg bez testów wolnych/e2e:

```
set PREPUSH_PYTEST_FAST=1   # Windows (cmd) – opcjonalnie
export PREPUSH_PYTEST_FAST=1 # bash/zsh – opcjonalnie
python -m pytest -q
```

Pełny bieg + raport JUnit do `reports/junit.xml`:

```
mkdir -p reports
python -m pytest -q --junitxml=reports/junit.xml
```

Uruchomienie wyłącznie minimalnych testów UI (a11y) dla statycznych stron:

```
python -m pytest -q tests/web/test_a11y_static_pages.py
```

## Szybki smoke API (lokalnie)

Uruchom API Gateway lokalnie i sprawdź zdrowie:

```
python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
# w drugim oknie
curl -s http://127.0.0.1:8000/health
```

Smoki skryptowe (bez serwera):

```
python scripts/smokes/openapi_smoke.py
python scripts/smokes/metrics_smoke.py
```

## Push (gałąź robocza)

Wypychamy zmiany na `feat/docs-cleanup` (PR bazuje na `work/daily`).

```
git push -u origin HEAD:feat/docs-cleanup
```

Po zielonych bramkach PR łączymy do `work/daily`; następnie automatyczna promocja do `main` zgodnie z regułami repo.

