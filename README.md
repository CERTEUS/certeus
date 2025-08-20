+======================================================================+
| CERTEUS — Prime Repository |
+======================================================================+
| PLIK / FILE: README.md |
| ROLA / ROLE: |
| PL: Dokument główny repo: struktura, standardy, uruchomienie, CI. |
| EN: Primary repo doc: structure, standards, bootstrap, CI. |
+======================================================================+

# CERTEUS — Verifiable Cognitive Intelligence (VCI)

> „Czysty kod to czyste myśli.” // "Clean code is clear thinking."

CERTEUS to inżynieria jakości, dowód i porządek – kernel prawdy + mikroserwisy
z bramką dowodową. Ten plik prowadzi Cię przez **strukturę repo**, **standard
kodowania (banery + docstringi PL/EN)**, **uruchomienie (Windows/macOS/Linux)**
oraz **CI/QA**. Zero partyzantki. NASA-poziom rzemiosła.

---

## Spis treści / Table of Contents

1. [Architektura w skrócie / Architecture at a glance] (#architektura)
2. [Struktura repo / Repository structure] (#struktura)
3. [Standard Kodowania (banery, docstringi, PL/EN)] (#standard)
4. [Szybki start (Windows & Unix)] (#start)
5. [Jakość i CI (Ruff, pre-commit, Proof Gate)] (#jakosc)
6. [Konwencje commitów i branchy] (#konwencje)
7. [Zasady bezpieczeństwa i provenance] (#security)
8. [Wkład / Contributing] (#contrib)
9. [Licencja i prawa] (#licencja)

---

## 1) Architektura w skrócie < a name="architektura"></a >

- **Kernel Prawdy (Truth Engine)** — kontrakt `verify(assumptions)` z dwoma
  solverami SMT (Z3/CVC5) i flagą `mismatch`.
- **Mikroserwisy** (ingest → map → verify → export) — API jedynie orkiestruje,
  nie implementuje logiki dziedzinowej.
- **Proof Gate (CI)** — każdy PR generuje artefakty dowodów (`.drat`/`.lfsc`)
  i uruchamia zewnętrzne weryfikatory; merge bez dowodu jest blokowany.
- **Packs/ i Schemas/** — reguły/benchmarki i jedyne źródło prawdy struktur
  (wersjonowane `*_vN.json`).

---

## 2) Struktura repo < a name="struktura"></a >

├─ services/ # Mikroserwisy (API Gateway, ingest/export/ledger/...)
│ └─ api_gateway/
│ ├─ main.py # FastAPI app (health, ingest, verify, export, sipp...)
│ └─ routers/ # /v1/ingest, /v1/export, /v1/sipp, /v1/verify...
│
├─ kernel/ # Truth Engine, SMT translator, dual-core adapters
│ ├─ dual_core/ # Z3/CVC5 adapters
│ └─ ... # verify(), mismatch protocol, etc.
│
├─ plugins/ # Rozszerzalność: exporter_pl, lexlog_rules_pl, ...
│
├─ clients/
│ └─ web/
│ ├─ proof_visualizer/ # Wizualizacja dowodów (stub i UI skeleton)
│ └─ tpl_diff/ # Diff TPL (UI skeleton)
│
├─ scripts/ # check_drat.sh, check_lfsc.sh, generate_proofs.py, ...
├─ tools/ # normalize/fix_certeus_headers.py (banery/docstrings)
├─ tests/ # e2e + services + truth + utils (pytest)
├─ .github/workflows/ # tests.yml, proof-gate.yml, security-scan.yml
└─ README.md

Zasady struktury: API = orkiestracja; dowody z artefaktami i checkiem zewnętrznym;
schematy i reguły wersjonowane; rozbudowa przez `plugins/`.

---

## 3) Standard Kodowania — Premium Code Style < a name="standard"></a >

**Zawsze** na górze pliku:

- **Baner** (box ASCII) z nazwą, rolą (PL/EN).
- **Docstring / komentarz modułu** (PL/EN, krótko, konkretnie).
- Sekcje w kodzie z wyraźnymi nagłówkami:
  `# === KONFIGURACJA / CONFIGURATION ===`, `# === LOGIKA / LOGIC ===` itd.

**Przykład (Python):**

```python
# +-------------------------------------------------------------+
# |                CERTEUS - Ingest Service (API)               |
# +-------------------------------------------------------------+
# | PLIK / FILE: services/ingest_service/models.py              |
# | ROLA / ROLE:                                                |
# |  PL: Modele danych ingestu (fakty, źródła, metryki).        |
# |  EN: Ingest data models (facts, sources, metrics).          |
# +-------------------------------------------------------------+

"""PL: Modele danych dla ingest. EN: Data models for ingest."""
from __future__ import annotations

# === IMPORTY / IMPORTS ===
# ...

# === MODELE / MODELS ===
# ...
Przykład (Shell):

#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                    CERTEUS - DRAT Checker                   |
# +-------------------------------------------------------------+
# | PLIK / FILE: scripts/check_drat.sh                          |
# | ROLA / ROLE:                                                |
# |  PL: Weryfikacja plików DRAT (stub/real).                   |
# |  EN: DRAT files verification (stub/real).                   |
# +-------------------------------------------------------------+
set -Eeuo pipefail
# ...


Przykład (HTML):

<!--
+-------------------------------------------------------------+
|            CERTEUS - Proof Visualizer (Skeleton)            |
+-------------------------------------------------------------+
| FILE: clients/web/proof_visualizer/index.html               |
| ROLE: Placeholder UI for interactive proof graph.           |
+-------------------------------------------------------------+
-->
<!DOCTYPE html>
<html lang="pl">...</html>


Nazewnictwo: pliki snake_case, klasy PascalCase, funkcje/zmienne snake_case,
stałe UPPER_CASE. Każda publiczna funkcja/klasa ma docstring PL/EN.

4) Szybki start (Windows & Unix) <a name="start"></a>

Wymagania: Python 3.11+, uv (do zarządzania deps), pre-commit.

Windows (PowerShell):

# 1) Utwórz i aktywuj venv
python -m venv .venv
.\.venv\Scripts\Activate.ps1

# 2) Zainstaluj narzędzia i zależności
pip install uv
uv sync

# 3) Zainstaluj pre-commit hooki
pre-commit install

# 4) Uruchom testy i linty
uv run ruff check .
uv run ruff format --check
uv run pytest -q

# 5) Dev server (FastAPI)
uv run uvicorn services.api_gateway.main:app --reload --port 8000


macOS/Linux (bash):

python -m venv .venv
source .venv/bin/activate
pip install uv
uv sync
pre-commit install
uv run ruff check .
uv run ruff format --check
uv run pytest -q
uv run uvicorn services.api_gateway.main:app --reload --port 8000

5) Jakość i CI (Ruff, pre-commit, Proof Gate) <a name="jakosc"></a>

pre-commit: uruchamia Ruff lint/format i nasze bramki (banery/docstringi).
Blokuje commit, jeśli coś nie spełnia standardu.

CI (tests.yml): checkout, uv sync, Ruff check/format (—check), pytest.

Proof Gate (proof-gate.yml): generacja artefaktów + zewnętrzna weryfikacja
(scripts/check_drat.sh, scripts/check_lfsc.sh). Na start mogą być stuby;
docelowo wpinamy drat-trim i weryfikator LFSC.

6) Konwencje commitów i branchy <a name="konwencje"></a>

Conventional Commits: feat:, fix:, chore:, docs:, refactor:,
test:, ci: …

Branże: feat/…, fix/…, chore/…. PR musi przejść Proof Gate i testy.

7) Zasady bezpieczeństwa i provenance <a name="security"></a>

Każdy raport/eksport i dowód posiada hash (sha256), timestamp oraz ścieżki
do artefaktów. Ledger nagłówkiem przekazuje łańcuch sha256:…;sha256:….

Publikacja i archiwizacja artefaktów dowodowych odbywa się wg polityk repo
(CI + scripts/).

8) Wkład / Contributing <a name="contrib"></a>

Upewnij się, że masz baner + docstring PL/EN w każdym nowym pliku.

Uruchom lokalnie: pre-commit run -a, pytest -q.

Dodaj test(y) do każdej zmiany publicznego kontraktu.

PR musi przejść CI + Proof Gate.

9) Licencja i prawa <a name="licencja"></a>

© CERTEUS. Wszelkie prawa zastrzeżone w ramach projektu.
Kontakt: maintainerzy projektu.


**Dlaczego to jest „stabilny” README?**
– Podsumowuje i **ujednolica** Twoje standardy „Premium Code Style” (banery, docstringi, PL/EN) oraz „Szynę Jakości” (pre-commit, Ruff, Proof Gate) – dokładnie to masz w swoim README oraz dokumentach VCI/Dziennika, które narzucają jakość, automaty i strukturę (tests/proof-gate/workflows).

---

### Szybkie résumé: co mamy „na zielono” po Dniu 11

- Spójny standard plików (banery, docstringi, PL/EN) i narzędzia lint/format. :contentReference[oaicite:15]{index=15}
- CI/workflows (tests, proof-gate), skrypty checkerów (stub), testy repo – przechodzą.
- Orkiestracja usług przez API (ingest/verify/export/sipp) – trzymamy kontrakty testów (ledger header, fields).
- Szkielety UI (proof visualizer / tpl diff) gotowe do rozbudowy. (Cockpit Architekta – kierunek rozwoju). :contentReference[oaicite:18]{index=18}

# CERTEUS — Verifiable Cognitive Intelligence (VCI)

> „Czysty kod to czyste myśli.” // "Clean code is clear thinking."

CERTEUS to inżynieria jakości, dowód i porządek — kernel prawdy + mikroserwisy z **Proof Gate**.
Ten dokument jest Twoim stabilnym punktem startu: **struktura repo**, **standard kodowania (banery + docstringi PL/EN)**,
**uruchomienie**, **CI/QA**, **bezpieczeństwo/provenance**.

---

## Architektura (w skrócie / at a glance)

- **Truth Engine** — kontrakt `verify(assumptions)` z dwoma solverami (Z3/CVC5) + flaga `mismatch`.
- **Mikroserwisy** — ingest → map → verify → export (API tylko orkiestruje).
- **Proof Gate (CI)** — PR generuje artefakty (`.drat`/`.lfsc`) i odpala zewnętrzne checkery; bez dowodu nie ma merge.
- **Packs/** i **Schemas/** — wersjonowane reguły i kontrakty JSON (AnswerContract, PCA², Provenance).

---

## Struktura repo (skrót)

``
services/      # FastAPI API Gateway + routers (ingest/verify/export/sipp/mismatch/ledger)
kernel/        # Truth Engine + dual_core adapters (z3/cvc5) + mismatch protocol
plugins/       # Rozszerzenia: exporter_pl, isap_adapter_pl, lexlog_rules_pl, tpl_diff_pl
packs/         # Jurysdykcje, reguły LEXLOG i benchmarki (PL/286 k.k. itd.)
schemas/       # answer_contract_v1.json, pca2_v1.json, provenance_receipt_v1.json
scripts/       # generate_proofs.py + check_drat.sh + check_lfsc.sh + validate_schemas.py
tests/         # e2e + services + truth + plugins
.github/workflows/  # tests.yml, proof-gate.yml, security-scan.yml
```

---

## Szybki start (Windows/macOS/Linux)

```bash
# 1) Virtualenv + deps
python -m venv .venv && source .venv/bin/activate    # Windows: .\.venv\Scripts\Activate.ps1
pip install uv && uv sync

# 2) Pre-commit
pre-commit install

# 3) Lint + test
uv run ruff check .
uv run ruff format --check
uv run pytest -q

# 4) Dev server (FastAPI)
uv run uvicorn services.api_gateway.main:app --reload --port 8000
```

---

## Jakość i CI

- **pre-commit**: banery/docstringi PL/EN + Ruff.
- **tests.yml**: lint, format (—check), pytest.
- **proof-gate.yml**: generuje artefakty + zewnętrzny check przez `scripts/check_*.sh`.

---

## Standard Kodowania — Premium Code Style (skrót)

- Baner ASCII + rola (PL/EN) na górze każdego pliku.
- Komentarze dwujęzyczne (PL/EN) dla publicznych funkcji/klas.
- Sekcje z nagłówkami (`# === LOGIKA / LOGIC ===`, etc.).
- Nazewnictwo: `snake_case` dla funkcji/zmiennych, `PascalCase` dla klas.

> Pełna wersja: `docs/coding_style.md` (przenieś dotychczasowe README do tego pliku).

---

## Bezpieczeństwo i Provenance

- Każdy eksport/dowód: `sha256 + timestamp + ścieżki artefaktów` (Truth Bill / Provenance Receipt).
- Ledger: chain‑of‑custody dla wejść, transformacji i eksportów.

---

## Konwencje

- **Commity**: Conventional Commits (`feat:`, `fix:`, `docs:`, `test:`, `ci:`…).
- **Branche**: `feat/*`, `fix/*`, `chore/*`, `refactor/*`.
- **SemVer**: `0.x` do wyjścia z MVP.

---

## Wkład / Contributing (TL;DR)

1. Dodajesz baner + docstring PL/EN.
2. `pre-commit run -a` i `pytest -q` lokalnie.
3. Pilnujesz kontraktów w `schemas/` (walidacja w CI).
4. PR przechodzi `tests.yml` + `proof-gate.yml`.

---

© CERTEUS — Verifiable Cognitive Intelligence.
