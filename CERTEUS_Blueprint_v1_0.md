# CERTEUS — Mapowanie Repo i Plan Rozbudowy (Blueprint v1.0)

**Zakres:** analiza `certeus.zip` (repo /mnt/data/certeus_repo/certeus), inwentaryzacja + rekomendacja, jak wpiąć nową fizykę-geometrię-pomiar (CFE/lexqft/QTMP) oraz pakiety domenowe (prawo/finanse/technologie).

## 0) TL;DR — budować na tym, co jest

- **Nie przepisywać od zera.** Repo ma zdrowy szkielet (kernel + mikroserwisy + schemas + tests).
- **Plan:** dodać trzy nowe warstwy jako **moduły first-class** + dopiąć bramki w CI i „boundary ledger”.

## 1) Inwentaryzacja (skrót)

- Liczba plików (po wycięciu vendorów): **399**
- Top katalogi (liczba plików / rozmiar):
  - `services`: 82 plików, 320.9KB
  - `tests`: 78 plików, 329.3KB
  - `scripts`: 44 plików, 195.6KB
  - `plugins`: 17 plików, 24.7KB
  - `kernel`: 16 plików, 45.3KB
  - `core`: 14 plików, 59.5KB
  - `clients`: 11 plików, 97.5KB
  - `packs`: 10 plików, 2.3KB
  - `docs`: 9 plików, 6.9KB
  - `.github`: 8 plików, 10.7KB
  - `runtime`: 7 plików, 11.7KB
  - `ingest_repo`: 6 plików, 2.0MB
  - `policies`: 6 plików, 12.2KB
  - `certeus.egg-info`: 5 plików, 1.5KB
  - `architectus`: 4 plików, 111.0B
  - `ops`: 4 plików, 653.0B
  - `proof-artifacts`: 4 plików, 276.0B
  - `schemas`: 4 plików, 18.2KB
  - `tools`: 4 plików, 35.1KB
  - `utils`: 4 plików, 10.5KB
- Najczęstsze rozszerzenia: `.pyc`×150, `.py`×124, `.md`×30, `.json`×16, `.yaml`×14, `.txt`×10, `<none>`×8, `.yml`×6, `.pdf`×4, `.sh`×4, `.xlsx`×3, `.html`×3
- **Uwaga:** w ZIP-ie są artefakty `.pyc` i `.venv` — do usunięcia z repo (dodaj do `.gitignore`).

## 2) Co już jest (mocne strony)

- **Kernel SMT/Truth Engine** (`kernel/`), **API Gateway** i serwisy (`services/*`), **schemas** (`provenance_receipt_v1.json`, itp.).
- **Proof Gate** (DRAT/LFSC) w CI, **tests/** ~78 plików.
- Zaczynające się wątki: `qtm`/`lexqft` (szkielety), `boundary/ledger_service`, `zkp_service`.

## 3) Luki względem naszej wizji (CFE/lexqft/QTMP)

- **CFE (geometria sensu):** brak pełnej implementacji metryki/krzywizn i geodezji; dodać moduł `cfe/` + telemetria `cfe.*`.
- **Holograficzny boundary-ledger:** ujednolicić `ledger_service` → `boundary.append()` + `bulk_reconstruct()`; KPI: `boundary.delta_bits`=0.
- **lexqft (UV):** tylko szkielety; potrzebny `compile/calibrate/sample` + integracja z kernelflow.
- **QTMP (pomiar):** dopiąć operatorowe pomiary w UI/routers + PCO (`qtm.*`).
- **PNIP / UPN:** warstwa sieciowa i identyfikatory są szczątkowe — dodać bibliotekę PNIP (proof-native HTTP/gRPC).

## 4) Architektura docelowa (nowe moduły)

```
core/
kernel/
modules/
  cfe/        # metryka g, Ricci(Forman/Ollivier), geodezje, horyzont, lensing
  lexqft/     # Lagranżjan, couplings, sampler/HMC, RG-flow
  qtm/        # funkcja falowa, operatory, komutatory, POVM, kanały dekoherencji
services/
  cfe_service/    # HTTP gRPC: /curvature /geodesic /horizon /lensing
  qtm_service/    # /measure /uncertainty /entanglement
  boundary_service/  # append-only ledger + bulk_reconstruct()
plugins/
  packs-law/ packs-fin/ packs-med/ packs-tech  # domain adapters
schemas/
  *_vN.json + boundary_event_v1.json + cfe_metrics_v1.json + qtm_events_v1.json
ops/
  ci/
    gates: gauge_gate.yaml, path_coverage_gate.yaml, boundary_rebuild_gate.yaml
```

## 5) Plan migracji (90 dni)

### Faza I (0–30 dni) — Higiena + Boundary + Telemetria

- Usuń `.venv/`, `.pyc`, `.pyd`, `.dll` z repo; uciśnij `.gitignore`.
- `services/ledger_service` → `boundary_service`: wprowadź `boundary_evt{upn,role,act,t,sig,meta}` i `bulk_reconstruct()`; KPI: `boundary.delta_bits`=0.
- Telemetria PCO: dodaj pola `cfe.*`, `qtm.*`, `boundary.*`.
- PNIP v0: middleware w API Gateway: podpis/odcisk request/response + `provenance_receipt_v1`.

### Faza II (30–60 dni) — CFE + Geodezje + Gates

- `modules/cfe`: metryka z GNN + Ricci(Forman) na grafie klauzul, API: `/curvature`, `/geodesic`, `/horizon`, `/lensing`.
- Scheduler ↔ `cfe.lapse_N` (dylatacja czasu prawnego) → throttling i progi ABSTAIN.
- CI: **Gauge-Gate** (holonomia sensu), **Boundary-Rebuild Gate** (δ=0), **Path-Coverage Gate** (dla lexqft).

### Faza III (60–90 dni) — lexqft + QTMP + Domeny

- `modules/lexqft`: `compile/calibrate/sample` (sampler HMC lub MCMC), `yukawa` dla Precedonu, RG-flow (β-funkcje).
- `modules/qtm`: pomiary (`measure_projective/POVM`), komutatory, kanały dekoherencji; UI: „Pytanie=Operator”.
- Pakiety domenowe: `packs-law` (LEXENITH), `packs-fin` (reguły AML/KYC/ryzyko), `packs-med` (zgoda, HIPAA/Rodo), `packs-tech` (licencje, patenty).

## 6) Interfejsy (kontrakty) — wklej do repo

**Boundary**

```json
{
  "upn": "urn:upn:...",
  "role": "processor|controller|auditor",
  "act": "consent_grant|consent_revoke|access|transform|publish",
  "t": "2025-08-30T12:00:00Z",
  "sig": "ed25519:...",
  "meta": { "jurisdiction": "PL", "law_time": "2025-08-30" }
}
```

**CFE API**

```http
GET /v1/cfe/curvature?case_id=...   -> { R:..., Ricci_max:..., kappa_max:... }
POST /v1/cfe/geodesic { facts:..., norms:... } -> { path:[...], action:... }
POST /v1/cfe/horizon { region:... } -> { locked:true, mass:4.2 }
```

**QTMP API**

```http
POST /v1/qtm/measure { basis:"verdict", amplitudes:{ALLOW:1, DENY:i, ABSTAIN:0.2} } -> { outcome:"ALLOW", p:0.62 }
GET  /v1/qtm/uncertainty?ops=L,T -> { lower_bound: 0.17 }
```

## 7) CI Gates (definicje skrótem)

- **Gauge-Gate:** fail jeśli `cfe.kappa_max > ε`; zestaw transformacji: język/jurysdykcja/nowelizacje.
- **Boundary-Rebuild Gate:** fail jeśli `boundary.delta_bits != 0` dla snapshotu doby.
- **Path-Coverage Gate:** minimalne `lexqft.coverage_gamma` i maks `uncaptured_mass`.

## 8) Mapowanie na katalogi w repo (gdzie dotknąć kodu)

- `kernel/` → hook na `cfe` (geodezja w `truth_engine`), `lexqft` (sampler), `qtm` (kolaps).
- `services/api_gateway` → middleware PNIP + rejestracja nowych routerów `cfe` i `qtm`.
- `services/ledger_service` → refactor do `boundary_service` + Merkle/append-only.
- `schemas/` → nowe schematy: `boundary_event_v1`, `cfe_metrics_v1`, `qtm_event_v1`.
- `tests/` → dodać testy conformance: pętla cechowania / horyzont / pomiar niekomutujących operatorów.

## 9) Ryzyka & jak je zbijamy

- **Koszt obliczeń (geodezje/UV)**: tryb „adaptive hotspots” (pełny solver tylko w regionach dużej krzywizny).
- **Identyfikowalność metryki**: regularizacja CFE-residuum + testy ablacją materiału dowodowego.
- **UX pomiaru**: wyraźne oznaczenie operatorów i kolejności; log każdy kolapsu (`qtm.*`).

## 10) „Gotowe do merge” — checklista

- [ ] `.gitignore` z `/.venv`, `*.pyc`, `*.pyd`, `*.dll`, `*.exe`
- [ ] `modules/cfe` + `services/cfe_service` + telemetria `cfe.*`
- [ ] `modules/qtm` + `services/qtm_service` + telemetria `qtm.*`
- [ ] `modules/lexqft` (compile/calibrate/sample + RG)
- [ ] `boundary_service` + `bulk_reconstruct()` + `boundary.delta_bits`=0
- [ ] CI Gates: gauge / boundary / path-coverage
- [ ] Pakiety domenowe: `packs-law` start (LEXENITH) + manifest integracyjny
- [ ] Dashboard PCO: karty `Geometry`, `Quantum`, `Boundary`
