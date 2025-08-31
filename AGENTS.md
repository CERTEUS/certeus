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

