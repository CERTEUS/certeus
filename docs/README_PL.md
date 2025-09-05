# CERTEUS - Przewodnik Szybkiego Startu (PL)

[![Tests](https://github.com/CERTEUS/certeus/actions/workflows/tests.yml/badge.svg)](https://github.com/CERTEUS/certeus/actions/workflows/tests.yml)
[![Smoke](https://github.com/CERTEUS/certeus/actions/workflows/smoke.yml/badge.svg)](https://github.com/CERTEUS/certeus/actions/workflows/smoke.yml)
[![Smoke Summary](https://img.shields.io/badge/smoke-summary-blue?logo=github)](https://github.com/CERTEUS/certeus/actions/workflows/smoke.yml)

Ten dokument zawiera w pełni poprawną, zwięzłą i praktyczną wersję instrukcji uruchomienia, testów i obserwowalności w języku polskim.

## 60 sekund: uruchom i sprawdź

- Linux/macOS

```
python -m venv .venv && source .venv/bin/activate
python -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn
python -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
# w drugim oknie
curl -s http://127.0.0.1:8000/health
```

- Windows (PowerShell)

```
py -3.11 -m venv .venv; .\\.venv\\Scripts\\Activate.ps1
$py = ".\\.venv\\Scripts\\python.exe"
& $py -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn
& $py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000
# w drugim oknie
curl.exe -s http://127.0.0.1:8000/health
```

Jeśli `py/python` wskazuje na stub WindowsApps (problem z utworzeniem venv), zainstaluj Pythona:

```
winget install -e --id Python.Python.3.11 --silent --accept-package-agreements --accept-source-agreements
```

Następnie powtórz komendy tworzące venv.

## Lint i testy

```
python -m ruff check . --fix && python -m ruff format .
python -m pytest -q --junitxml="reports/junit.xml"
```

## Dev stack (Docker Compose)

```
make run-stack   # uruchamia API+ProofGate+Prometheus+Grafana
make smoke       # szybki test końcowy (E2E)
make down-stack  # zatrzymanie stacka
```

- Grafana: <http://localhost:3000> (admin/admin)
- Prometheus: <http://localhost:9090>

## Najważniejsze endpointy (MVP)

- POST `/v1/pco/bundle` — buduje i waliduje ProofBundle v0.2; status i wpis do ledger (przez ProofGate).
- GET `/pco/public/{case_id}` — publiczny payload (zero PII); weryfikacja Merkle + Ed25519.
- GET `/.well-known/jwks.json` — JWKS (klucz publiczny Ed25519).
- GET `/metrics` — metryki Prometheus (SLO, liczniki, histogram p95).
- POST `/v1/sources/cache` — cache źródeł prawa (digest + ścieżka).
- POST `/v1/proofgate/publish` — decyzja wg Policy Pack (PUBLISH/CONDITIONAL/PENDING/ABSTAIN).

## Przykłady cURL

Zobacz `docs/curl_examples.md` — komplet wywołań (bundle, public PCO, JWKS, metrics, sources/cache, ProofGate, ledger API, E2E).

## Klucze i JWKS

- ENV/files: `ED25519_PRIVKEY_PEM`, `ED25519_PUBKEY_B64URL`.
- Vault (opcjonalnie): `KEYS_BACKEND=vault`, `VAULT_ADDR`, `VAULT_TOKEN`, `VAULT_SECRET_PATH`.
- Szczegóły: `docs/security/key_management.md`.

## Obserwowalność

- Prometheus rules: `observability/prometheus/recording_rules.yml`.
- Dashboard Grafana: `observability/grafana/certeus-slo-dashboard.json` (import automatyczny w dev stacku).

## Manifest

- Bieżący: `docs/manifest_v1_7.md` (linkowany również z README).

---

## Smoke & E2E (DEV/CI)

- Uruchomienie lokalne:
  - Windows: `pwsh -File .\scripts\smoke_api.ps1`
  - Linux/macOS: `bash ./scripts/smoke_api.sh`
- Kryteria przejścia (domyślne):
  - Wszystkie sprawdzane endpointy zwracają 2xx (zero `fails`).
  - `p95_ms` z podsumowania smoke (liczony z `/metrics` histogramu `certeus_http_request_duration_ms_bucket`) ≤ `SLO_MAX_P95_MS` (domyślnie 250 ms w DEV).
  - Skrypty zwracają kod wyjścia ≠ 0 przy błędach (fail CI).
- Pytest e2e:
  - `tests/e2e/test_smoke_endpoints.py` – wykorzystuje `TestClient`, generuje tymczasowy klucz Ed25519, ustawia izolowane katalogi na bundle/cache.
- Wskazówki debugowania:
  - JWKS/PCO: uruchom `pwsh -File .\scripts\keys_dev.ps1`, potem `. .\scripts\env_load.ps1` (PS) lub `source ./scripts/dev_env.sh` (bash); sprawdź `/.well-known/jwks.json`.
  - Weryfikatory proofów: ustaw `PROOF_VERIFY_DEBUG=1`; do szybkiej diagnostyki możesz użyć `PROOF_VERIFIER_MOCK=lfsc_ok` lub `drat_ok`.
  - P95: powtórz smoke lokalnie i sprawdź `/metrics`; problemy zwykle wynikają z zimnego startu albo konfliktów portów.
  - Multipart: w Windows używamy `curl.exe -F ...` (Invoke-RestMethod bywa wrażliwy na boundary i typy MIME).
  - Tolerancja błędów: można ustawić `SMOKE_MAX_FAILS` (domyślnie 0) do tymczasowej tolerancji w DEV/CI.

---

## Demo T13 — Marketplace & Packs (ABI/SemVer)

- Bramka Marketplace (report‑only): `python scripts/gates/marketplace_policy_gate.py`
- Bramka ABI/SemVer (report‑only): `python scripts/gates/pack_abi_semver_gate.py`
- Aktualizacja baseline ABI: `python scripts/packs/update_abi_baselines.py`

Ścieżka deweloperska (skrót):

1. Wprowadź zmianę w module pluginu (np. sygnatura `register`).
2. Uruchom `python scripts/gates/pack_abi_semver_gate.py` — oczekiwane ostrzeżenie/violation przy braku bumpu MAJOR.
3. Zrób bump MAJOR w `plugins/<name>/plugin.yaml` (`version: 2.0.0`).
4. Zaktualizuj baseline: `python scripts/packs/update_abi_baselines.py`.
5. Zweryfikuj w CI (ci‑gates publikuje wynik gate’ów jako komentarz w PR).

Polityka SemVer dla packs: zobacz `docs/guides/packs_abi_semver.md`.

## Demo T14 — Billing & A11y/i18n

1. A11y/i18n
   - Strony web mają skip‑link do `#main`, widoczne focusy; UI wspiera PL/EN (nagłówek `Accept-Language` + `?lang` → `Content-Language`).
2. Billing & Cost‑tokens
   - Sekwencja demo (PowerShell/bash):

```
# Billing (tenant quota + allocate + refund)
$env:TENANT = 't-demo'
curl.exe -s http://127.0.0.1:8000/v1/billing/quota -H "X-Tenant-ID: $env:TENANT"
curl.exe -s -X POST http://127.0.0.1:8000/v1/billing/quota -H 'content-type: application/json' -d '{"tenant":"t-demo","units":3}'
curl.exe -s -X POST http://127.0.0.1:8000/v1/billing/allocate -H 'content-type: application/json' -H "X-Tenant-ID: $env:TENANT" -d '{"cost_units":2}'
curl.exe -s -X POST http://127.0.0.1:8000/v1/billing/refund   -H 'content-type: application/json' -H "X-Tenant-ID: $env:TENANT" -d '{"units":1}'

# Tokens request → allocate → status
$rid = (curl.exe -s -X POST http://127.0.0.1:8000/v1/fin/tokens/request -H 'content-type: application/json' -d '{"user_id":"u123","amount":50,"purpose":"compute"}' | ConvertFrom-Json).request_id
curl.exe -s http://127.0.0.1:8000/v1/fin/tokens/$rid
curl.exe -s -X POST http://127.0.0.1:8000/v1/fin/tokens/allocate -H 'content-type: application/json' -d '{"request_id":"'$rid'","allocated_by":"ops"}'
curl.exe -s http://127.0.0.1:8000/v1/fin/tokens/$rid

# Packs — list and try
curl.exe -s http://127.0.0.1:8000/v1/packs/
curl.exe -s -X POST http://127.0.0.1:8000/v1/packs/try -H 'content-type: application/json' -d '{"pack":"demo_report_pl","kind":"summarize","payload":{"title":"My Report","items":[1,2,3,4]}}'
```

- Ustal limit: `POST /v1/billing/quota {tenant, units}` (demo‑admin)
- Sprawdź balans: `GET /v1/billing/quota`
- Rezerwuj: `POST /v1/billing/allocate {cost_units}` → `ALLOCATED` lub `PENDING`
- Zwrot: `POST /v1/billing/refund {units}`

3. Marketplace Install/Upgrade
   - `POST /v1/packs/install {pack, signature, version?}` — zapisuje podpis i wersję zainstalowaną; UI: `/app/public/marketplace.html` (przycisk Install/Upgrade)

## Demo T15 — QTMP API & SDK

1) QTMP (cURL)

```
curl -sS -X POST http://127.0.0.1:8000/v1/qtm/init_case -H 'content-type: application/json' -d '{"case":"LEX-001","basis":["ALLOW","DENY","ABSTAIN"]}'
curl -i  -sS -X POST http://127.0.0.1:8000/v1/qtm/measure -H 'content-type: application/json' -d '{"operator":"L","case":"LEX-001","source":"doc"}' | sed -n '1,30p'
curl -sS -X POST http://127.0.0.1:8000/v1/qtm/measure_sequence -H 'content-type: application/json' -d '{"operators":["L","T","W"],"case":"LEX-001"}'
curl -sS -X POST http://127.0.0.1:8000/v1/qtm/decoherence -H 'content-type: application/json' -d '{"case":"LEX-001","channel":"dephasing","gamma":0.2}'
```

2) SDK (Python)

```
from sdk.python.certeus_sdk import CerteusClient

cli = CerteusClient(base_url="http://127.0.0.1:8000")
cli.qtm_init_case(case="LEX-001", basis=["ALLOW","DENY","ABSTAIN"])
resp = cli.qtm_measure(operator="L", case="LEX-001", source="sdk:demo")
print(resp.pco_headers.get("X-CERTEUS-PCO-qtm.collapse_event"))
print(cli.qtm_measure_sequence(operators=["L","T","W"], case="LEX-001").data)
```

## CFE — przykłady domenowe (Geometry of Meaning)

 ```bash 
curl -sS \ http://127.0.0.1:8000/v1/cfe/lensing?domain=MED\ | jq

curl -sS -X POST \\
  \http://127.0.0.1:8000/v1/cfe/horizon\ \\
  -H 'Content-Type: application/json' \\
  -d '{\case\:\MED-CASE-CRIT-1\,\domain\:\MED\,\severity\:\critical\}' | jq
```

```
