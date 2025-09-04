<!--
+-------------------------------------------------------------+
|                          CERTEUS                            |
+-------------------------------------------------------------+
| FILE: README.md                                            |
| ROLE: Repo landing (Quickstart).                             |
| PLIK: README.md                                            |
| ROLA: Strona startowa repo (Szybki start).                   |
+-------------------------------------------------------------+
-->

# CERTEUS — Quickstart

Dowód, nie opinia. Verifiable Cognitive Intelligence.

Najważniejsze instrukcje uruchomienia lokalnego i odnośniki do dokumentacji.

## Uruchom lokalnie

- Linux/macOS

```
python -m venv .venv && source .venv/bin/activate
python -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn
python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
```

- Windows (PowerShell)

```
py -3.11 -m venv .venv; .\.venv\Scripts\Activate.ps1
$py = ".\\.venv\\Scripts\\python.exe"
& $py -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn
& $py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
```

Sprawdź: `curl -s http://127.0.0.1:8000/health`

## Cockpit (UI)

Przeglądaj w przeglądarce po uruchomieniu API:

- Geometry: `http://127.0.0.1:8000/app/public/geometry.html`
- Quantum: `http://127.0.0.1:8000/app/public/quantum.html`
- Boundary (jeśli włączony): `http://127.0.0.1:8000/app/public/boundary.html`

## ChatOps / MailOps (cURL)

Przykłady:

```
curl -s -H 'Content-Type: application/json' \
  -d '{"cmd":"cfe.geodesic","args":{}}' \
  http://127.0.0.1:8000/v1/chatops/command | jq .

curl -s -H 'Content-Type: application/json' \
  -d '{"mail_id":"MAIL-001","from_addr":"alice@example.com","to":["ops@example.com"],"attachments":[]}' \
  http://127.0.0.1:8000/v1/mailops/ingest | jq .
```

Więcej przykładów: `docs/cookbooks/chatops_mailops.md`.

## Smoke (szybki test E2E)

- PowerShell: `pwsh -File scripts/smoke_api.ps1`
- Bash: `bash scripts/smoke_api.sh`

## Lint i testy

```
python -m ruff check . --fix && python -m ruff format .
python -m pytest -q --junitxml=reports/junit.xml
```

## Proof‑Only I/O (opcjonalnie)

Wymuś dowodową publikowalność dla wybranych ścieżek:

```
# Windows PS
$env:STRICT_PROOF_ONLY = '1'
# Linux/macOS
export STRICT_PROOF_ONLY=1
```

Bez tokenu PCO wybrane ścieżki (np. POST `/v1/mailops/ingest`) zwrócą `403` (DROP: proof‑required).

## Dokumentacja

- PL quickstart rozszerzony: `docs/README_PL.md`
- Dev setup (krok po kroku): `docs/guides/dev-setup.md`
- API/OpenAPI: `docs/api/*`, runtime: `http://127.0.0.1:8000/docs`
- Cockpit/operacje: `docs/cookbooks/chatops_mailops.md`
- Agent Hub: `docs/AGENTS/README.md`

