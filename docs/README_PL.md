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

1) Wprowadź zmianę w module pluginu (np. sygnatura `register`).
2) Uruchom `python scripts/gates/pack_abi_semver_gate.py` — oczekiwane ostrzeżenie/violation przy braku bumpu MAJOR.
3) Zrób bump MAJOR w `plugins/<name>/plugin.yaml` (`version: 2.0.0`).
4) Zaktualizuj baseline: `python scripts/packs/update_abi_baselines.py`.
5) Zweryfikuj w CI (ci‑gates publikuje wynik gate’ów jako komentarz w PR).

Polityka SemVer dla packs: zobacz `docs/guides/packs_abi_semver.md`.
