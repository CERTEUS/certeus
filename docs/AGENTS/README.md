# CERTEUS - Agent Hub (One-Stop)

Ten hub zbiera w jednym miejscu wszystkie istotne materiały dla agenta:

- Handoff i status prac: `docs/AGENTS/HANDOFF.md`
- Reguły pracy (skrót): `AGENTS.md` (plik źródłowy w repo‑root)
- Roadmapa 90 dni: `docs/90_dni_work.md`
- WORKLOG (dziennik): `WORKLOG.md`
- Manifest / standard kodowania: `docs/manifest.md`, `docs/manifest_v1_7.md`
- Runbooki bezpieczeństwa i ról: `docs/runbooks/security_bunker.md`, `docs/runbooks/roles_governance.md`
- Dashboardy/alerty SRE: `observability/grafana/certeus-sre-dashboard.json`, `observability/prometheus/alert_rules_w10.yml`

## Gałęzie i automatyzacja

- Gałąź robocza: `work/daily` (zielona) – zmiany agenta trafiają tutaj.
 - Auto-promocja TYLKO tygodniowa: do `main` promujemy wyłącznie po zakończeniu tygodnia i zielonych checkach:
  - commit na `work/daily` musi zawierać marker `[week-end]` lub trailer `weekly-promote: true`.
  - Wymagane checki (Branch Protection): `Smoke (ubuntu-latest)`, `Smoke (windows-latest)`, `ci-gates`.
  - Gate’y informacyjne (PR‑only): Gauge‑Gate, Path‑Coverage‑Gate, Boundary‑Rebuild‑Gate, asset‑guard; Proof Gate — push: main, PR: main.
  - PR summary (ci‑gates) publikuje ticki gate’ów/smoków/workflowów + trend perf.
- OTel w CI: włączony mock OTLP (`scripts/otel/mock_otlp.py`), `OTEL_ENABLED=1`.

## Smoki / SLO / Perf (w CI i lokalnie)

- Smoki in‑proc (bez uruchamiania serwera):
  - `/metrics`: `scripts/smokes/metrics_smoke.py`
  - `/openapi.json`: `scripts/smokes/openapi_smoke.py`
  - ProofGate `/healthz`: `scripts/smokes/proofgate_health_smoke.py`
- Perf bench: `scripts/perf/quick_bench.py` → `out/perf_bench.json` (artefakt); trend porównywany z `ci-status:ci/perf_bench.json`.
- SLO smoke: `scripts/slo_gate/measure_api.py` + `scripts/slo_gate/check_slo.py` (domyślne progi p95=300 ms, error‑rate 1%).

## Polityki / Gate’y bezpieczeństwa

- Role OPA/Rego: `policies/security/roles.rego` (+ Governance Pack `policies/governance/governance_pack.v0.1.yaml`).
- ProofGate enforcement (domena lex/fin/sec) – włączany flagą `FINE_GRAINED_ROLES` (w testach CI domyślnie = 0).
- Bunkier/TEE: `scripts/gates/security_bunker_gate.py` (+ stub `security/bunker/attestation.json`).
- PQ‑crypto: `scripts/gates/pqcrypto_gate.py` (informacyjny lub wymagany przez `PQCRYPTO_REQUIRE=1`).
- DP budgets: `scripts/gates/dp_budget_gate.py` (stub; `STRICT_DP_BUDGET=1` wymusza znaczenie).

## Flagi środowiskowe (CI defaults)

- `.github/certeus.env.defaults` ładowane przez `scripts/ci/load_env_defaults.py`.
- Kluczowe: `BUNKER`, `PROOFGATE_BUNKER`, `FINE_GRAINED_ROLES`, `PQCRYPTO_READY`, `PQCRYPTO_REQUIRE`, `STRICT_DP_BUDGET`.
- OTel: `OTEL_ENABLED=1`, `OTEL_EXPORTER_OTLP_ENDPOINT=http://127.0.0.1:4318` (mock OTLP).

## Punkty wejścia / pliki kluczowe

- Workflows: `.github/workflows/ci-gates.yml`, `.github/workflows/proof-gate.yml`.
- Skrypty gate’ów i smoków: `scripts/gates/*`, `scripts/smokes/*`, `scripts/slo_gate/*`, `scripts/perf/*`, `scripts/otel/mock_otlp.py`.
- Usługi: `services/api_gateway/main.py` (middleware p95; OpenAPI cache), `services/proofgate/app.py` (enforcement ról; OpenAPI cache).

## Notatki operacyjne

- Skrypty odpalane „jako plik” wymagają repo‑root w `sys.path` — wzorzec: dopisać `Path(__file__).resolve().parents[2]` do `sys.path` i zignorować E402 (`# noqa`).
- Legacy testy ProofGate (decyzje) oczekują wyłączonego enforcementu ról — w CI kroki „Tests” mają `FINE_GRAINED_ROLES=0`.

## Historia (reset i archiwa)

- 2025‑09‑02 wykonano reset historii do pojedynczego „root commit” (czytelna baza).
- Poprzednia historia dostępna wyłącznie w archiwach: `origin/archive/old-main-*`, `origin/archive/old-daily-*`.
- Na widoku `main`/`work/daily` widoczny jest tylko bieżący, uporządkowany stan.

## Onboarding (5 minut)

1) Klon i środowisko
   - `python -m venv .venv && source .venv/bin/activate` (Windows: `py -3.11 -m venv .venv; .\.venv\Scripts\Activate.ps1`)
   - `python -m pip install -U pip wheel setuptools ruff pytest fastapi uvicorn jsonschema cryptography`
2) Lint + testy lokalnie
   - `python -m ruff check . --fix && python -m ruff format .`
   - `mkdir -p reports && python -m pytest -q --junitxml=reports/junit.xml`
3) Uruchomienie API in‑proc (szybki smoke)
   - `python scripts/smokes/openapi_smoke.py` • `python scripts/smokes/metrics_smoke.py`
4) Push roboczy
   - `python scripts/git_push.py --to work/daily`
5) CI
   - Sprawdź ticki w komentarzu PR/ci‑gates. Jeśli czerwone — patrz „Troubleshooting”.

## Daily SOP (TL;DR)

UWAGA: Auto‑promocja następuje wyłącznie po zakończeniu tygodnia — commit musi zawierać marker `[week-end]` lub trailer `weekly-promote: true`.

- Przyjmij issue/task z Roadmapy (docs/90_dni_work.md).
- Zrób zmianę minimalną, lint+test na lokalnym.
- Push na `work/daily` → obserwuj CI (gates + smokes + workflows).
- Jeśli wszystkie zielone → auto‑promocja do `main`/auto‑merge PR.
- Dopisz wpis do `WORKLOG.md` (skrypt: `scripts/worklog/update_worklog.py`).

## CI Gates — co musi być zielone

- Proof Gate (workflow: `.github/workflows/proof-gate.yml`)
  - Kroki Gate’ów: Gauge / Path‑Coverage / FIN Policies / Bunker / Roles / Governance / Boundary / SLO.
  - Publikujemy ticki per‑krok (pliki `out/pg_*_ok.txt` i komentarz PR).
- asset‑guard — sprawdza obecność assetów brandu.
- Gauge‑Gate, Path‑Coverage‑Gate, Boundary‑Rebuild‑Gate — stuby/metyka (akceptują wartości domyślne).

## Auto‑merge — jak działa

- Repo ma włączone `allow_auto_merge`; branch‑protection ustawione na approvals=0.
- PR z `work/daily`→`main` scali się automatycznie po komplecie zielonych checków.
- PR summary (ci‑gates) publikuje ticki i trend perf, ułatwiając decyzję.

## Troubleshooting (czerwone)

- ModuleNotFoundError w skryptach (Perf/SLO/Smokes):
  - Dopisz do skryptu: `from pathlib import Path; import sys; sys.path.insert(0, str(Path(__file__).resolve().parents[2]))` oraz `# noqa: E402` przy imporcie aplikacji.
- ProofGate testy wpadają w ABSTAIN:
  - Upewnij się, że kroki „Tests” w workflow mają `FINE_GRAINED_ROLES=0` (legacy); enforcement testy sterują flagą lokalnie.
- Supply‑chain (Trivy) blokuje PR:
  - Włączone `exit-code: '0'` — raport idzie jako SARIF; jeśli znów blokuje, sprawdź konfigurację workflow.
- asset‑guard fail:
  - Zweryfikuj pliki brandu: `docs/assets/brand/*` i `clients/web/public/brand/*` — brakujące uzupełnij lub zamockuj.
- Proof Gate kroki:
  - Komentarz w PR ma ticki per‑krok; sprawdź logi kroku w workflow (Gauge/Path/Bunker/itd.).

## Konwencje i bezpieczeństwo

- Commity: Conventional Commits (feat/fix/chore/docs/ci/perf…).
- Gałęzie PR: `merge/daily-to-main-YYYYMMDD-HHMMSS` (automatyczne tworzenie do merge).
- Tokeny: `.devkeys/admin_token.txt` (lokalnie; nie publikować), `GITHUB_TOKEN` w CI; nigdy nie wklejać do logów/PR.

## Zasada niezmienna (Immutable Rule)

"Publikuj wyłącznie to, co jest jawnie dozwolone przez obowiązującą allowlistę LITE; wszystko inne pozostaje prywatne, a każdy push respektuje bramki i ochronę gałęzi (bez wyjątków)."

Praktyka:
- Pracuj prywatnie (repo główne), testuj lokalnie/CI; publiczny mirror utrzymuj jako LITE‑surface (README, landing, assets, overview, lekkie CI).
- Gdy masz wątpliwość – nie publikuj; dopisz do allowlisty wyłącznie po akceptacji i z pełną świadomością konsekwencji.
- Nigdy nie omijaj gate’ów (gitleaks/policy‑scan/branch‑protection) i nie publikuj poza allowlistą.
