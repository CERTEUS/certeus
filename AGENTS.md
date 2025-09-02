# CERTEUS — AGENTS.md (reguły dla agenta)

Uwaga: Centralny hub dokumentacji agenta przeniesiony do:
`docs/AGENTS/README.md` (zawiera skróty do WORKLOG/90_dni/manifestów, bramek i runbooków).

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
`git push -u origin HEAD:work/daily`

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

### Procedura pracy (każda sesja)

1) Lint + testy: `ruff check . --fix`, `ruff format .`, `pytest -q`.
2) Push roboczy: `venv/bin/python scripts/git_push.py --to work/daily` (Windows: `.\.venv\Scripts\python.exe scripts\git_push.py --to work/daily`).
3) CI uruchamia gate’y. Jeśli wszystkie zielone → auto‑promocja do `main`. Jeśli którekolwiek `failure` → automatyczne Issue; agent naprawia i ponawia push.
4) Nigdy nie wklejamy tokenów do logów/PR; sekrety tylko w ENV lub w `.devkeys/*.txt` (ignorowane).

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
- Idempotencja: skrypty pomocnicze (apply_headers/apply_*_headers) mogą być uruchamiane wielokrotnie; nie duplikują nagłówków.


## Plan 90 dni (Roadmapa)

- Dokument źródłowy:  — zawiera pełną mapę tygodni (18×5 dni).
- Zasady:
  - Agent realizuje zadania tydzień po tygodniu, w kolejności i z DOD.
  - Po każdym ukończonym zadaniu: update  (skrót + szczegóły), commit na  i monitorowanie gate’ów.
  - Po „zielonych” gate’ach commit automatycznie ląduje na .
  - Jeśli gate’y spadną: Gate‑Failure‑Notify otwiera Issue — agent naprawia i kontynuuje.
- Minimalny SOP tygodnia:
  - Przeczytaj zakres w  (np. Tydzień 7 — FINENITH v0.1),
  - Dostarcz API/PCO/UI/gate’y z DOD,
  - Uzupełnij README (demo tygodnia) i AGENTS/WORKLOG,
  - Wypchnij na  i potwierdź zielony stan.

## Handoff / Stan prac (skrót)
- Historia wyczyszczona (single‑root commit, 2025‑09‑02). Archiwa starej historii: `origin/archive/old-main-*`, `origin/archive/old-daily-*`.
- Gałęzie: `main` = zielony; `work/daily` = zielony.
- CI/PR podsumowanie: ci‑gates publikuje komentarz z tickami (style/lint/tests/perf/slo/smokes) + statusy workflowów (Proof Gate / Gauge / Path‑Coverage / Boundary / asset‑guard) oraz trendem perf p95.
- OTel w CI: włączony mock OTLP (`scripts/otel/mock_otlp.py`) + `OTEL_ENABLED=1` — ślady są przyjmowane lokalnie.
- Smoki in‑proc: `/metrics`, `/openapi.json`, ProofGate `/healthz`.
- SLO/Perf: quick bench (p95) zapisuje `out/perf_bench.json` (artefakt), SLO smoke mierzy i weryfikuje progi.
- Dashboards: `observability/grafana/certeus-sre-dashboard.json` (p95 by path/method/status, error‑rate, p95 staty).
- Pełny opis i następne kroki: `docs/AGENTS/HANDOFF.md`.
