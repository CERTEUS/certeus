# W17 Demo — Go‑to‑Market

## Cel
Pokaż landing, sandbox QTMP, public PCO oraz polityki billing (tiering). Wszystko lokalnie.

## Start
- Uruchom API Gateway:
  - Windows: `.\\.venv\\Scripts\\python.exe -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`
- Otwórz `http://127.0.0.1:8000/` (landing → `/app/public/index.html`).

## Ścieżka demo
1) Landing: sekcja Quick checks
   - Wpisz `X-Tenant-ID` (np. `acme`), kliknij „Check tier” i „Check balance”.
   - Wybierz akcję (np. `qtm.measure`) i kliknij „Estimate cost”.
2) QTMP Sandbox
   - „Try now: QTMP sandbox” → `/app/public/qtm.html`
   - `Init case` → `Measure L→T` / `T→L` → sprawdź UB i collapse w nagłówkach.
3) Public PCO
   - W landing wpisz RID/`case_id` (np. `CER-LEX-001`) i kliknij „Open Public PCO”.
4) Polityki i OpenAPI
   - `/v1/billing/policies` — podgląd domyślnych tierów i mapowania tenants.
   - `/openapi.json` — kontrakt runtime (testy porównują z `docs/api/openapi.yaml`).

## Weryfikacja
- Lint: `ruff check . --fix && ruff format .`
- Testy: `pytest -q`
- Oczekiwane: 125 passed, 1 skipped (lokalne): zielono.

## Notatki
- Tier „anonymous” = `free` (domyślne). Zmienisz przez `runtime/billing/policies.json` lub `BILLING_POLICY_FILE`.
- Endpoint `/v1/billing/estimate` używa wbudowanej tabeli kosztów (MVP) i zwraca `estimated_units`.

