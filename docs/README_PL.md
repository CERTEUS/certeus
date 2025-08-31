# CERTEUS — Przewodnik Szybkiego Startu (PL)

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
- Grafana: http://localhost:3000 (admin/admin)
- Prometheus: http://localhost:9090

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

