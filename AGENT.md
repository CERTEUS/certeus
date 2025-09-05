# CERTEUS — AGENT.md (reguły dla agenta)

Uwaga: Centralny hub dokumentacji agenta znajduje się w:
`docs/AGENTS/README.md` (skrót do WORKLOG/90_dni/manifestów, bramek i runbooków).

Zasada niezmienna (TL;DR):

Publikujemy wyłącznie to, co jest jawnie dozwolone przez allowlistę LITE (mirror publiczny). Wszystko inne zostaje w repo prywatnym i przechodzi przez bramki (gitleaks/policy‑scan/branch‑protection) — bez wyjątków.

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

## Pre-commit (lokalna dyscyplina)

- Instalacja: `$py -m pip install pre-commit`
- Aktywacja w repo: `pre-commit install`
- Ręczne uruchomienie na całym repo: `pre-commit run -a`
- Włączone hooki:
  - `ruff` (lint + format)
  - `normalize: section spacing (python)` — porządkuje puste linie wokół sekcji (Sekcja 21)
  - `prettier` (md/yaml/json/html/js/css)
  - `pytest (fast)` — szybka weryfikacja na zmianach py

## Pre-push (lokalna bramka)

- Ścieżka hooków: `git config core.hooksPath .githooks` (ustawione w repo).
- Hook: `.githooks/pre-push` — uruchamia:
  - Premium Style Gate: `scripts/check_premium_style.py` (Sekcja 21),
  - `ruff check .` oraz `ruff format --check`,
  - `pytest -q` (pełen zestaw). Skrócony bieg: ustaw `PREPUSH_PYTEST_FAST=1` (uruchomi bez `slow/e2e`).
- Interpreter: preferuje lokalny `.venv_cli/Scripts/python.exe`, w fallback `python3/python` z PATH.

## Testy

`mkdir -Force reports`
`$py -m pytest -q --junitxml="reports\junit.xml"`

## Serwer

`$py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000`

## Push

`git add -A`
`git commit -m "chore: lint+tests via Codex" --no-verify`
`git push -u origin HEAD:work/daily`

UWAGA (oszczędzanie minut GH Actions): push/PR wykonujemy tylko na koniec w pełni ukończonego tygodnia pracy (wg 90‑dniowego planu). W trakcie tygodnia pracujemy lokalnie, uruchamiając `ruff` i `pytest` bez błędów.

## Auto‑push i auto‑promocja (operacje agenta)

- Gałąź robocza: `work/daily` (agent wypycha zmiany tutaj).
- Auto‑promocja do `main` po zielonych bramkach:
  - Wymagane checki (Branch Protection): `Smoke (ubuntu-latest)`, `Smoke (windows-latest)`, `ci-gates`.
  - Gate’y informacyjne (PR‑only): Gauge‑Gate, Path‑Coverage‑Gate, Boundary‑Rebuild‑Gate, asset‑guard, Proof Gate (push: main; PR: main).
  - Workflow `.github/workflows/promote-daily-to-main.yml` nasłuchuje `ci-gates` i promuje `work/daily → main` (FF/PR auto‑merge).
- Powiadomienia o porażkach: `.github/workflows/gate-failure-notify.yml` otwiera/aktualizuje Issue z linkiem do błędnego gate’u i blokuje promocję do `main` do czasu naprawy.

### Uwierzytelnianie push (agent)

- Preferowane: `gh auth login` + `gh auth setup-git` w środowisku, w którym uruchamiany jest agent.
- Alternatywy wspierane przez helpera `scripts/git_push.py`:
  - ENV: `ADMIN_TOKEN` (PAT z prawem write) i opcjonalnie `GITHUB_USER`.
  - Pliki lokalne (ignorowane w repo):
    - `.devkeys/admin_token.txt` – jedna linia z PAT,
    - `.devkeys/github_user.txt` – jedna linia z loginem GitHub.
- Helper automatycznie:
  - pobiera token z ENV → `gh auth token` → pliku `.devkeys/admin_token.txt`,
  - ustala właściciela repo z `origin`,
  - ustala login z ENV/pliku/API `/user`,
  - zapisuje poświadczenia do `.git-credentials` (ignorowane) i wykonuje `git push`.

### Zasady oszczędzania minut (GH Actions)

- Nie wypychamy drobnych commitów — łączymy pracę tygodnia w jeden push/PR.
- Gate’y informacyjne są PR‑only; wymagane checki: `Smoke (ubuntu/windows)`, `ci-gates`.
- W trakcie tygodnia testujemy lokalnie (`ruff check`, `ruff format`, `pytest -q`) i naprawiamy u siebie.

### Watcher CI (live podgląd workflowów)

- Skrypt: `scripts/ci/watch_ci.ps1` — bezpieczny podgląd statusów GH Actions.
- Token: bierze z `GITHUB_TOKEN` → `ADMIN_TOKEN` → `.devkeys/admin_token.txt` → `gh auth token`.
- Snapshot (jednorazowo): `pwsh -File scripts/ci/watch_ci.ps1 -Once`
- Live (co 30 s, gałąź `work/daily`):
  - `pwsh -File scripts/ci/watch_ci.ps1 -Branch work/daily -Interval 30`
- Tylko wybrany workflow (np. `ci-gates.yml`):
  - `pwsh -File scripts/ci/watch_ci.ps1 -Branch work/daily -Workflow ci-gates.yml -Interval 30`
- Skrypt nie wypisuje sekretów; nie logować tokenów w konsoli/PR.

### Procedura pracy (każda sesja)

1. Lint + testy: `ruff check . --fix`, `ruff format .`, `pytest -q`.
2. Push roboczy: `venv/bin/python scripts/git_push.py --to work/daily` (Windows: `.\.venv\Scripts\python.exe scripts\git_push.py --to work/daily`).
3. CI uruchamia gate’y. Jeśli wszystkie zielone → auto‑promocja do `main`. Jeśli którekolwiek `failure` → automatyczne Issue; agent naprawia i ponawia push.
4. Nigdy nie wklejamy tokenów do logów/PR; sekrety tylko w ENV lub w `.devkeys/*.txt` (ignorowane).

### WORKLOG (dziennik prac)

- Plik: `WORKLOG.md` (repo‑root). Zawiera krótkie wpisy z datą, gałęzią i skrótem zmian.
- Aktualizacja (automatyczna/pół‑automatyczna) przy pomocy skryptu:
  - `venv/bin/python scripts/worklog/update_worklog.py --summary "W5: Quantum cockpit + presets API" --details "- /v1/qtm/preset\n- Grafana dashboard"`
- Każdy agent po wykonaniu zadań dopisuje wpis (maks. 1–2 linie + punkty szczegółów), aby inne sesje miały świeży kontekst.

## Premium Code Style (Sekcja 21 — rdzeń agenta)

- Standard: Każdy plik musi mieć baner CERTEUS na górze oraz docstring modułu PL/EN (patrz: `docs/manifest.md` — 21) Standard Kodowania).
- Sekcje w kodzie: agent utrzymuje znaczniki struktury pliku w Pythonie i skryptach: `# === IMPORTY / IMPORTS ===`, `# === KONFIGURACJA / CONFIGURATION ===`, `# === MODELE / MODELS ===`, `# === LOGIKA / LOGIC ===`, `# === I/O / ENDPOINTS ===`, `# === TESTY / TESTS ===`.
- Proof‑native: wejście PNIP i publikowalne wyjścia PCO są first‑class; nie logujemy sekretów; OTel w API (zob. 21.3–21.5).
- Linty/testy: ruff/pytest są bramką jakości; agent uruchamia `ruff check . --fix`, `ruff format .`, `pytest` przed push.
- Automatyzacja: w CI działa gate `scripts/check_premium_style.py` (wymusza banery/docstringi/sekcje). Workflow: `.github/workflows/ci-gates.yml`.
- Idempotencja: skrypty pomocnicze (apply*headers/apply*\*\_headers) mogą być uruchamiane wielokrotnie; nie duplikują nagłówków.

## Plan 90 dni (Roadmapa)

- Dokument źródłowy: — zawiera pełną mapę tygodni (18×5 dni).
- Zasady:
  - Agent realizuje zadania tydzień po tygodniu, w kolejności i z DOD.
  - Po każdym ukończonym zadaniu: update (skrót + szczegóły), commit na i monitorowanie gate’ów.
  - Po „zielonych” gate’ach commit automatycznie ląduje na .
  - Jeśli gate’y spadną: Gate‑Failure‑Notify otwiera Issue — agent naprawia i kontynuuje.
- Minimalny SOP tygodnia:
  - Przeczytaj zakres w (np. Tydzień 7 — FINENITH v0.1),
  - Dostarcz API/PCO/UI/gate’y z DOD,
  - Uzupełnij README (demo tygodnia) i AGENTS/WORKLOG,
  - Wypchnij na i potwierdź zielony stan.

## Handoff / Stan prac (skrót)

- Historia wyczyszczona (single‑root commit, 2025‑09‑02). Archiwa starej historii: `origin/archive/old-main-*`, `origin/archive/old-daily-*`.
- Gałęzie: `main` = zielony; `work/daily` = zielony.
- CI/PR podsumowanie: ci‑gates publikuje komentarz z tickami (style/lint/tests/perf/slo/smokes) + statusy workflowów (Proof Gate / Gauge / Path‑Coverage / Boundary / asset‑guard) oraz trendem perf p95.
- OTel w CI: włączony mock OTLP (`scripts/otel/mock_otlp.py`) + `OTEL_ENABLED=1` — ślady są przyjmowane lokalnie.
- Smoki in‑proc: `/metrics`, `/openapi.json`, ProofGate `/healthz`.
- SLO/Perf: quick bench (p95) zapisuje `out/perf_bench.json` (artefakt), SLO smoke mierzy i weryfikuje progi.
- Dashboards: `observability/grafana/certeus-sre-dashboard.json` (p95 by path/method/status, error‑rate, p95 staty).
- Pełny opis i następne kroki: `docs/AGENTS/HANDOFF.md`.

## CI/Runner — tryb „0 minut” (self‑hosted)

- Runnery:
  - Windows self‑hosted (poza repo) — Promote i kroki administracyjne.
  - Linux self‑hosted (Docker) — ci‑gates, Smoke, Release, Mirror; gotowe compose w `infra/gha-runner/`:
    - Windows (Docker Desktop): `docker compose -f docker-compose.yml -f docker-compose.windows.yml up -d`
    - Linux: `docker compose -f docker-compose.yml -f docker-compose.linux.yml up -d`
    - Token rejestracyjny (ephemeral): `gh api -X POST repos/CERTEUS/certeus/actions/runners/registration-token -q .token` → wpisz do `infra/gha-runner/.env` jako `RUNNER_TOKEN=`.
    - Obraz: `myoung34/github-runner:latest` (Docker Hub) z labelami: `self-hosted,linux,docker,build`.

- Zmienne repo (sterowanie runnerami):
  - `CI_GATES_RUNS_ON` — np. `["self-hosted","linux","docker","build"]`
  - `RELEASE_RUNS_ON` — jw.
  - `PROMOTE_RUNS_ON` — np. `["self-hosted"]`
  - `MIRROR_RUNS_ON` — jw. (opcjonalnie GH‑hosted dla public „free”)
  - `SMOKE_USE_GH_HOSTED` — `0/1` (fallback dla Smoke)
  - `REQUIRE_COSIGN_ATTESTATIONS` — `1` (wymuszenie cosign dla SBOM/provenance)

## Workflowy — zasady i optymalizacje

- `ci-gates`:
  - cache pip (`actions/setup-python@v5` + `cache: pip`),
  - testy równoległe (`pytest-xdist`): `-n auto --durations=15`.
- `smoke`:
  - `dorny/paths-filter@v3` — ciężkie kroki Smoke odpalane tylko przy istotnych zmianach (services/scripts/clients/web/docs-api/pyproject/requirements),
  - wczesny short‑circuit („No smoke-relevant changes”).
- `canary_gate` (PR‑only):
  - `permissions: pull-requests: write` (komentarz p95 do PR),
  - deps: `fastapi httpx uvicorn cryptography jsonschema openapi-spec-validator python-multipart z3-solver`.
- `repo-tree`: heredoc → `REPO_TREE.md` (bez błędów parsera).
- `release`: SBOM/provenance + cosign keyless (assets Release) + PCO bundle; wspiera `workflow_dispatch(tag)`.
- `promote-daily-to-main`:
  - marker tygodnia: `[week-end] …` lub `weekly-promote: true`,
  - cross‑platform (github‑script/pwsh), 
  - `workflow_dispatch` z `force=true` (awaryjnie),
  - auto‑PR i auto‑merge (GraphQL) gdy FF niemożliwy.

## Poświadczenia agenta (lokalnie)

- Pliki (ignorowane):
  - `.devkeys/admin_token.txt` — PAT (repo:write)
  - `.devkeys/github_user.txt` — login GitHub
- Alternatywa: `gh auth login` + `gh auth setup-git`.
- Loader: `scripts/env_load.ps1` zapisuje do `~/.git-credentials` i ustawia helper `store`.

## Higiena repo i sprzątanie

- `.gitignore` obejmuje: `venv/.venv/.venv_cli`, `node_modules`, `out/`, `reports/`, artefakty runnera (`_work/`, `_diag/`, `bin/`, `externals/`), `.devkeys/`, itp.
- Sprzątanie tylko ignorowanych: `pwsh -File scripts/tools/local_clean.ps1 -Yes` (bez ruszania śledzonych plików).

## SOP (dla zespołu)

- Dziennie:
  - `ruff check . --fix && ruff format . && pytest -q` (lokalnie można `-n auto`),
  - push na `work/daily`, wpis do `WORKLOG.md` (`scripts/worklog/update_worklog.py`).
- Tygodniowo:
  - commit z markerem `[week-end] …` + `weekly-promote: true`,
  - po zielonych gate’ach auto‑Promote → Mirror (LITE/allowlista).

## Monitoring (pod ręką)

- Lista biegów: `gh run list -L 10`
- Podgląd runu: `gh run view <id> -v`
- Checki PR: `gh pr checks <nr>`
