#!/usr/bin/env markdown

# CERTEUS — Agent Prompts (P0/P1)

Cel: przydział precyzyjnych zadań agentom, bez konfliktów (piaskownice ścieżek), z jasnym DOD i bramkami CI. Skopiuj odpowiedni prompt do okna agenta i uruchom pracę.

## Zasady wspólne (dla wszystkich agentów)

- Gałąź robocza: `feat/<obszar>-<skrót>` od `work/daily`; PR → `work/daily`.
- DOD (Definition of Done): zielone bramki wymagane: `Tests`, `UI Smoke`, `Canary‑Gate`, `truth‑gates`.
- Zakres edycji: tylko podane ścieżki (piaskownica). Nie dotykać innych obszarów.
- Commity: Conventional Commits. Pre‑commit włączony (`ruff`, `prettier`, guards).
- Dokumenty wewnętrzne: nie commitować (guard aktywny). Publiczne docs pod `docs/`.

---

## P0 — ProofFS 3× platformy (A5 lead; A6/A7 wsparcie)

Prompt (wklej agentowi A5):

```
Zadanie: ProofFS 3× (Linux/macOS/Windows) — xattrs PNIP/PCO (RO), mock mount/unmount API, UI inspektor xattrs, Asset‑Integrity Gate.

Branch: feat/prooffs-mount-xattrs

Edytuj tylko:
- core/pfs/**
- services/api_gateway/routers/pfs.py
- clients/web/public/pfs_inspector.html (nowy)
- scripts/gates/asset_integrity_gate.py (nowy)
- .github/workflows/ci-gates.yml (dodaj Asset‑Integrity Gate)

Nie dotykaj: services/proofgate/**, security/**, runtime/p2p_*.py

Kroki:
1) core/pfs: API xattrs PNIP/PCO (read‑only) + stub adapterów FUSE/Dokan (tylko interfejs/testy kontraktowe bez instalacji driverów w CI).
2) services/api_gateway/routers/pfs.py: endpointy RO: list/materialize/xattrs dla pfs:// URI.
3) UI: clients/web/public/pfs_inspector.html — inspektor xattrs (PNIP/PCO) dla podanego pfs://.
4) CI: scripts/gates/asset_integrity_gate.py (enforce) — weryfikacja spójności PNIP/PCO na próbkach.
5) .github/workflows/ci-gates.yml — dodaj gate jako required tick.

Testy/DOD:
- unit: URI/xattrs; integration: list/materialize/xattrs; e2e: (mock) mount→inspect→unmount.
- Wszystkie bramki zielone; brak regresji API.
```

---

## P0 — FROST 2‑z‑3 w ProofGate (A5 lead; A8 wsparcie)

Prompt (A5):

```
Zadanie: FROST 2‑z‑3 — agregacja podpisów, enforce w publish, zapis quorum do PCO/ledger, gate w CI.

Branch: feat/proofgate-frost-enforce

Edytuj tylko:
- security/frost.py (nowy)
- services/proofgate/app.py
- scripts/gates/proof_frost_enforce.py (nowy)
- .github/workflows/ci-gates.yml (dodaj FROST step)

Nie dotykaj: PFS/Devices/p2p/**, clients/web/**

Kroki: implementacja agregacji, ścieżki negatywne (0/1/3 podpisy), enforce przy REQUIRE_COSIGN_ATTESTATIONS=1, zapis quorum w PCO i ledger.

Testy/DOD: unit+integration+e2e publish; FROST gate required; bramki zielone.
```

---

## P0 — TEE/Bunker (RA→PCO) (A8 lead; A5/A6)

Prompt (A8):

```
Zadanie: TEE RA fingerprint → PCO; polityki bunkra on/off; wskaźniki TEE w UI; gate walidujący RA.

Branch: feat/tee-bunker-ra

Edytuj tylko:
- security/ra.py (nowy)
- services/api_gateway/security.py (middleware/polityki)
- services/proofgate/app.py (PCO z RA)
- clients/web/public/* (znacznik TEE)
- scripts/gates/security_bunker_gate.py (rozbudowa)

Nie dotykaj: core/pfs/**, runtime/p2p_*.py

Testy/DOD: unit RA, integration publish z RA, e2e bunker on/off; gate RA pass; bramki zielone.
```

---

## P0 — SYNAPSY P2P (transport) (A8 lead; A7)

Prompt (A8/A7):

```
Zadanie: Transport QUIC/Noise + (stub) SPIFFE/SPIRE; kolejka zdalna; integracja p2p routera; smoke P2P.

Branch: feat/p2p-transport-quic-noise

Edytuj tylko:
- runtime/p2p_transport.py (nowy)
- runtime/p2p_queue.py (rozszerzenie)
- services/api_gateway/routers/p2p.py
- scripts/smokes/p2p_smoke.py (nowy; report‑only)

Nie dotykaj: ProofGate/TEE, core/pfs/**

Testy/DOD: unit/integration (enqueue/status/dequeue), e2e Devices via P2P (report‑only na start), bramki zielone.
```

---

## P0 — Supply‑chain enforce (A8)

Prompt (A8):

```
Zadanie: Enforce SBOM/provenance + cosign; deny‑by‑default dla pluginów; CI gate.

Branch: feat/supply-chain-enforce

Edytuj tylko:
- scripts/gates/supply_chain_enforce.py (rozbudowa)
- .github/workflows/ci-gates.yml (enforce ścieżek pluginów; REQUIRED)
- docs/compliance/** (runbook)

Nie dotykaj: services/** poza minimalnymi ścieżkami artefaktów

Testy/DOD: policy tests; gate włączony; bramki zielone.
```

---

## P1 — SDK 2.0 (TS/Go) (A5/A6)

Prompt (A5/A6):

```
Zadanie: SDK klienci TS/Go, pełne metody QTMP/lexqft/ProofGate; SDK Contract Gate.

Branch: feat/sdk-ts-go

Edytuj tylko:
- sdk/ts/**, sdk/go/**
- clients/web/public/playground.html
- scripts/gates/sdk_contract_gate.py (nowy; na start report‑only)

Testy/DOD: kontrakty OpenAPI→SDK; smoke SDK; bramki zielone.
```

---

## P1 — LEXENITH pipeline (A6)

Prompt (A6):

```
Zadanie: Pipeline lock→motion→publish→Why‑Not (PCΔ) ze ścieżką PCO.

Branch: feat/lexenith-pipeline

Edytuj tylko:
- services/api_gateway/routers/lexenith.py
- integracje z ProofGate/ledger (tylko niezbędne)

Testy/DOD: integration + e2e (publikacja, ledger, export); tick w Proof Gate; bramki zielone.
```

---

## P1 — FIN/LEX dashboardy (A6)

Prompt (A6):

```
Zadanie: Panele FIN (sentyment/ryzyko/splątanie) i LEX (ścieżki/cytaty/CLDF) w UI.

Branch: feat/dashboards-fin-lex

Edytuj tylko:
- clients/web/public/fin.html, clients/web/public/lexenith.html

Testy/DOD: a11y smoke + snapshoty; bramki zielone.
```

---

## Test Owners (A1–A8) — tylko tests/**

Prompt (wzorzec):

```
Zadanie: [A1..A8] rozszerzenie testów w wyznaczonym obszarze. Tylko tests/** i ewentualnie scripts/** (helpers). Bez zmian runtime.

Branch: work/tests-aX-<obszar>

Edytuj tylko:
- tests/<obszar>/** oraz ewentualnie scripts/** do uruchomienia testów

Nie dotykaj: services/**, core/**, clients/**

Testy/DOD: zielone na PR; brak nowych ostrzeżeń istotnych.

Przykłady:
- A1 Ω: tests/truth/*, tests/omega/*
- A2 CFE: tests/services/test_cfe_*.py
- A3 QTMP: tests/services/test_qtm_*.py
- A4 LexQFT: tests/services/test_lexqft_*.py
- A5 ProofGate/PCO/Ledger/Boundary: tests/services/test_proofgate_*, test_pco_*, tests/boundary/*
- A6 UI/E2E/a11y: tests/web/*, tests/smokes/test_a11y_smoke.py
- A7 Devices/Packs: tests/services/test_devices_*, test_w14_packs_mvp.py
- A8 Security/Compliance/SRE: tests/gates/*, tests/services/test_security_*, perf/SLO smokes
```

---

## Notatki koordynacyjne

- Każdy agent pracuje „w ciemno” (brak wiedzy o innych), ale w ściśle odseparowanych ścieżkach.
- Konfiguracja Branch Protection już wymaga: `Tests`, `UI Smoke`, `Canary‑Gate`, `truth‑gates`.
- Auto‑promocje `work/daily → main` zostają bez zmian.

