## Dev setup — krok po kroku

### 1) Python i wirtualne środowisko

- Linux/macOS

```
python -m venv .venv && source .venv/bin/activate
python -m pip install -U pip wheel setuptools
```

- Windows (PowerShell)

```
py -3.11 -m venv .venv; .\.venv\Scripts\Activate.ps1
```

Jeśli `py/python` wskazuje na WindowsApps (nie tworzy venv):

```
winget install -e --id Python.Python.3.11 --silent --accept-package-agreements --accept-source-agreements
```

### 2) Zależności projektowe

```
python -m pip install -U ruff pytest jsonschema cryptography fastapi uvicorn openapi-spec-validator
```

### 3) Klucze i ENV (DEV)

```
# PowerShell
pwsh -File .\scripts\keys_dev.ps1
. .\scripts\env_load.ps1

# Bash
./scripts/keys_dev.ps1  # (w PowerShellu)
source ./scripts/dev_env.sh || true
```

### 4) Uruchom API

```
python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
```

Sprawdź: `curl -s http://127.0.0.1:8000/health`

### 5) Cockpit (UI)

- Geometry: `http://127.0.0.1:8000/app/public/geometry.html`
- Quantum: `http://127.0.0.1:8000/app/public/quantum.html`

### 6) ChatOps i MailOps (szybko)

```
curl -s -H 'Content-Type: application/json' -d '{"cmd":"cfe.geodesic","args":{}}' http://127.0.0.1:8000/v1/chatops/command | jq .
curl -s -H 'Content-Type: application/json' -d '{"mail_id":"MAIL-1","from_addr":"a@b","to":["ops@example.com"],"attachments":[]}' http://127.0.0.1:8000/v1/mailops/ingest | jq .
```

Więcej: `docs/cookbooks/chatops_mailops.md`.

### 7) Proof‑Only I/O (opcjonalnie)

```
export STRICT_PROOF_ONLY=1  # PS: $env:STRICT_PROOF_ONLY='1'
```

Wybrane ścieżki (np. `/v1/mailops/ingest`) wymagają tokenu PCO (bez niego: `403`).

### 8) Lint, testy i smoki

```
python -m ruff check . --fix && python -m ruff format .
mkdir -p reports && python -m pytest -q --junitxml=reports/junit.xml
pwsh -File ./scripts/smoke_api.ps1  # lub: bash ./scripts/smoke_api.sh
```

### 9) WORKLOG (po zadaniu)

```
python scripts/worklog/update_worklog.py --summary "W1: Cockpit + ChatOps/MailOps" --details "- Geometry/Quantum telemetry\n- ChatOps/MailOps smoke"
```

### 10) Push (tygodniowo)

Na koniec pełnego tygodnia pracy: `python scripts/git_push.py --to work/daily`.

Auto‑promocja do `main` nastąpi po zielonych gate’ach.
