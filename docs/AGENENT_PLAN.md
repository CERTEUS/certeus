## **0\) Role, zakres i własność katalogów (żeby nikt nikomu nie blokował PR)**

**Agent A1 – Ω‑Kernel & Transformacje**

* **Własność:** `/core/omega`, `/policies/gauge/`, testy: `tests/omega_*`

* **Cel:** niezmienniczość sensu (Gauge), mapy jurysdykcji/języka/ontologii, Gauge‑Gate.

**Agent A2 – CFE (Geometria Sensu)**

* **Własność:** `/modules/cfe/`, `/services/cfe/`, `clients/web/**/geometry*`

* **Cel:** Ricci/Ollivier‑Ricci, geodezyjne, horyzont, lensing.

**Agent A3 – QTMP (Pomiar)**

* **Własność:** `/modules/qtmp/`, `/services/qtm/`, `clients/web/**/quantum*`

* **Cel:** funkcja falowa spraw, komutatory L/T, dekoherecja, sekwencje pomiarów.

**Agent A4 – lexqft (Ścieżki/Zjawiska)**

* **Własność:** `/modules/lexqft/`, `/services/lexqft/`, `gate: path_coverage`

* **Cel:** tunelowanie, wirtualne pary, renormalizacja autorytetu, coverage‑gate.

**Agent A5 – Proof‑Pipeline (ProofGate/Ledger/Boundary/ProofFS)**

* **Własność:** `/services/proofgate/`, `/services/ledger/`, `/services/boundary_service/`, `/core/prooffS*/`, `/schemas/`

* **Cel:** Proof‑Only I/O, PCO schema & walidacja, Boundary reconstruct, OpenAPI & SDK publikacje.

**Agent A6 – Klienci & Operacje (Cockpit/ChatOps/MailOps)**

* **Własność:** `/clients/web/`, `/services/chatops/`, `/services/mail/`, `docs/guides/`

* **Cel:** UX (Geometry/Quantum/Boundary), a11y/i18n, ChatOps/MailOps cookbooki.

**Agent A7 – Domain Packs & Devices**

* **Własność:** `/plugins/packs-*/`, `/modules/devices/` (HDE, Q‑Oracle, Entangler, Chronosync)

* **Cel:** LEXENITH/FINENITH produkcyjnie \+ urządzenia 1.0→2.0.

**Agent A8 – SRE/Security/Compliance/Infra**

* **Własność:** `/.github/workflows/`, `/infra/**`, `/policies/security*/`, `/docs/adr/`, `/docs/sla.md`

* **Cel:** SLO, supply‑chain (SLSA/in‑toto/SBOM), PQ‑crypto/FROST, TEE, SYNAPSY/P2P, DR‑drills.

**Kodeks „bez kolizji”:**

* **CODEOWNERS** per katalog zgodnie z powyższym; **merge okno**: **środa 16:00–18:00** (A5→A1→A2→A3→A4→A7→A6→A8).

* **Branch prefiksy:** `a1/…`, `a2/…` itd.; jedna funkcja \= jeden PR; **„nie rozjeżdżamy manifestu”** – edytuje wyłącznie właściciel sekcji.

* **PIĄTEK 12:00** – „freeze tygodnia” → integracja i demo; **bez hotfixów** po freeze (wyjątek: P1).

---

## **1\) Rytm dnia (wszyscy agenci)**

* **09:00** stand‑up (10′), **11:30** cross‑sync tech‑leadów (10′), **16:30** gate‑check (10′).

* **Artefakt dnia:** PCO \+ wpis w Ledger \+ notka w `worklog.md` (auto‑commit).

* **Bramki codziennie:** Gauge ≤ 1e‑3 · Coverage ≥ 0.90 · Boundary Δbits \== 0 · Proof‑Only I/O.

---

## **2\) 90 dni → 18 tygodni (8 swimlane’ów równolegle)**

Poniżej rozpiska **per tydzień**: co dostarcza **każdy agent**. Każdy tydzień musi skończyć się **demo \+ PCO**.

### **Tydzień 1 — *Stabilizacja i telemetry core***

* **A1:** Holonomia cykli (lang/jur/ontology) – profil 1.0; raport `gauge.holonomy_drift`.

* **A2:** CFE: Ricci/Ollivier‑Ricci z realną metryką; p95 \< 200 ms.

* **A3:** QTMP: `qtm.sequence[]` \+ baseline komutatorów (L vs T).

* **A4:** lexqft: `/coverage` karmi gate realnymi metrykami (γ, uncaptured).

* **A5:** Proof‑Only I/O – pełne egzekwowanie w całym API; OpenAPI examples.

* **A6:** Cockpit: Geometry/Quantum telemetry (heatmapy \+ log sekwencji).

* **A7:** Devices bootstrap (HDE plan API), packs layout (LEX/FIN).

* **A8:** OTel+eBPF+profiling; powiązanie trace ↔ `correlation_id` ↔ PCO.

### **Tydzień 2 — *CFE v1.0 i PCO 1.1***

* **A1:** Transformacje jurysdykcji – regresy semantyczne (testy property‑based).

* **A2:** Geodezyjne (A\* na metryce) \+ Horyzont (lock) – PCO: `geodesic_action`, `horizon_mass`.

* **A3:** QTMP: kanały dekoherecji \+ `collapse_latency_ms`.

* **A4:** Tunelowanie (WKB‑like) – 2 scenariusze z kontrdowodami.

* **A5:** PCO v1.1 – walidatory w SDK; publikacja artefaktów podpisana.

* **A6:** Cockpit: przycisk „lock” i widoki horyzontu.

* **A7:** Q‑Oracle (expectation) – MVP; FIN pack: R/S operator base.

* **A8:** Supply‑chain: SLSA/in‑toto/SBOM (deny by default).

### **Tydzień 3 — *LEX/FIN – pierwsze wartości***

* **A1:** Mapy telos/litera (L/T) jako transformacje bazowe.

* **A2:** Lensing: mapa „critical\_precedents”.

* **A3:** Nieoznaczoność L·T – PCO: `uncertainty_bound.L_T`.

* **A4:** Wirtualne pary, `energy_debt` – budżetowane.

* **A5:** Boundary `bits_delta_map` per shard, snapshoty przyrostowe.

* **A6:** Operator Composer 1.0 w Cockpicie (presety).

* **A7:** FIN splątanie aktywów (MI) \+ pierwsze alerty; LEX Why‑Not export (PCΔ).

* **A8:** Rate‑limit \+ load‑shedding sterowany QTMP.

### **Tydzień 4 — *Devices v1.0***

* **A1:** Stabilizacja Gauge‑Gate (ε auto‑kalibracja na korpusach).

* **A2:** CFE perf tuning (cache krzywizn).

* **A3:** Splątanie dowodowe – metryki (MI/negativity) \+ alerting.

* **A4:** Renormalizacja autorytetu (`cldf.renorm.*`).

* **A5:** ProofFS: xattrs PNIP/PCO (RO) – Linux.

* **A6:** Cockpit: graf splątań i preset testów QTMP.

* **A7:** HDE – optymalizacja koszt/krzywizna; Entangler – `target_negativity`.

* **A8:** DR‑drill: Boundary shard fail → RTO/RPO w normie.

### **Tydzień 5 — *FINENITH v1.0 (pilot)***

* **A1:** Transformacje rynkowe (czas, strefa, rynki) – inwarianty.

* **A2:** CFE na danych FIN (normatywa rynków – compliance/prawo).

* **A3:** QTMP R̂/Ŝ – nieoznaczoność risk vs sentiment.

* **A4:** Path‑coverage karmione danymi FIN (γ≥0.9 real).

* **A5:** OpenAPI FIN \+ SDK; polityki ryzyka w PCO.

* **A6:** Dashboard FIN (sentyment+ryzyko+splątania).

* **A7:** `fin/alpha/measure` \+ PnL sym; pilot „paper trading” (sandbox).

* **A8:** Ochrona danych FIN: DP/ZK polityki (OPA/Rego).

### **Tydzień 6 — *LEXENITH v1.0 (pilot)***

* **A1:** Mapy rewizji prawa (wersjonowanie) – stabilność sensu.

* **A2:** Lensing dla najwyższych instancji (SN/TS).

* **A3:** `qtm.sequence[]` warianty (L→T vs T→L) – wizualizacja różnic.

* **A4:** Tunelowanie w sprawach spornych – scenariusze.

* **A5:** CLDF/LEX‑FONTARIUS – hash‑cytaty w PCO.

* **A6:** Generator pism (2 szablony) \+ Cockpit export.

* **A7:** Micro‑Court – pipeline lock→publish (PCO ścieżki).

* **A8:** DPIA/DPA mapowanie (LEX pakiet zgodności).

### **Tydzień 7 — *ProofFS 3× platformy***

* **A1:** Testy holonomii na plikach (PNIP jako transformacja).

* **A2:** Indeksy CFE w ProofFS (wgląd w krzywizny per plik/dowód).

* **A3:** Oznaczenia pomiarów jako extended attributes.

* **A4:** Ścieżki dowodowe serializowane w PFS (read‑only).

* **A5:** macFUSE/Dokan porty \+ notarization.

* **A6:** Cockpit: mount/unmount \+ inspektor xattrs.

* **A7:** Integracja packs z PFS (LEX/FIN).

* **A8:** Asset integrity gate: brak PCO/PNIP → nie montuj.

### **Tydzień 8 — *SYNAPSY P2P v1***

* **A1:** Semantyka transformacji w P2P (deterministyczna).

* **A2:** Mapy CFE replikowane (CRDT) dla nie‑krytycznych.

* **A3:** QTMP operator cache w edge nodes.

* **A4:** Dystrybucja ścieżek (DHT kompetencji).

* **A5:** PFS bridge P2P (content addressing).

* **A6:** Cockpit: status węzłów P2P.

* **A7:** Devices kolejkują zlecenia w P2P (HDE/Q‑Oracle).

* **A8:** QUIC/Noise transport \+ SPIFFE/SPIRE tożsamości.

### **Tydzień 9 — *PQ‑crypto \+ FROST***

* **A1:** Podpisy transformacji – ślady metryki.

* **A2:** Podpisy CFE (hybrydowe) – audytowalne krzywizny.

* **A3:** Pomiary z podpisem ML‑DSA.

* **A4:** Dowody ścieżek z podpisem (Merkle of paths).

* **A5:** FROST 2‑z‑3 w ProofGate – enforce publish.

* **A6:** UI: wizard podpisów i custody kluczy.

* **A7:** Devices podpisują output; packs polityki kluczy.

* **A8:** Rotacje kluczy, KMS/HSM, RA‑docs (Trust Center).

### **Tydzień 10 — *TEE profil***

* **A1‑A4:** RA fingerprint w PCO; ścieżki w bunkrze opcjonalnie.

* **A5:** ProofGate integracja RA; „bunkier on/off” per polityka.

* **A6:** UI: wskaźniki TEE w Cockpicie.

* **A7:** Devices w TEE (krytyczne operacje).

* **A8:** DR‑drill TEE: fail open/close bez naruszeń Proof‑Only.

### **Tydzień 11 — *FINENITH → produkcja***

* **A1‑A2:** Stabilizacja transformacji FIN.

* **A3:** R/S nieoznaczoność – alerty i raporty.

* **A4:** Coverage FIN ciągły.

* **A5:** SLA/limity, throttle & quotas.

* **A6:** Dashboardy produkcyjne.

* **A7:** 2 strategie Q‑Alpha z PCO/PnL.

* **A8:** Audyt bezpieczeństwa i compliance FIN.

### **Tydzień 12 — *LEXENITH → produkcja***

* **A1‑A2:** Lensing SN/TS, geodezyjne E2E.

* **A3:** Nieoznaczoność L/T – raport spraw.

* **A4:** Tunelowanie „trudnych spraw”.

* **A5:** DR‑Replay/Recall \+ UPN revoke.

* **A6:** Exporty pism i śladów (Citizen‑friendly).

* **A7:** Casebook pokazowy 3 sprawy.

* **A8:** Audyt prawny (zewnętrzny) z checklistą.

### **Tydzień 13 — *Marketplace & Billing***

* **A1‑A4:** ABI/semver kompatybilność packs.

* **A5:** Billing & Proof‑Cost tokens; „allocate → publish”.

* **A6:** Marketplace w Cockpicie.

* **A7:** 2 public packs (demo).

* **A8:** Licencje, podpisy, polityki.

### **Tydzień 14 — *Med/Sec/Code packs MVP***

* **A1‑A4:** Transformacje/specyfika domen.

* **A5:** PCO rozszerzenia DPCO/MCO/SEC.

* **A6:** UX widoki domenowe.

* **A7:** 3 MVP packi (MED/SEC/CODE).

* **A8:** DPIA/ISO/SOC2 mapowanie.

### **Tydzień 15 — *SRE 2.0***

* **A1‑A4:** Auto‑tuning workloads (QTMP‑aware).

* **A5:** Canary/progressive delivery.

* **A6:** Anomaly UX (alerts przyswajalne).

* **A7:** Devices retry/idempotency.

* **A8:** GameDay: boundary shard \+ P2P turbulencje.

### **Tydzień 16 — *SDK/DevEx 2.0***

* **A1‑A4:** Przykłady per moduł.

* **A5:** SDK py/ts/go – retry/idempotent/timeouty.

* **A6:** Playground w Cockpicie (copy/paste) \+ try‑now.

* **A7:** Sample repos (FIN/LEX/MED/SEC/CODE).

* **A8:** Contract‑tests w CI na bazie OpenAPI.

### **Tydzień 17 — *Pilotaże 2.0***

* **A1‑A4:** Telemetria pod piloty.

* **A5:** Multi‑tenant SLO i izolacja.

* **A6:** UX „pilot feedback loop”.

* **A7:** 3 piloty (LEX/FIN/MED).

* **A8:** Bezzałogowe DR‑procedury.

### **Tydzień 18 — *GTM & Launch 2.0***

* **A1‑A4:** Code freeze \+ RC (zielone bramki).

* **A5:** Tag, release, changelog, social preview.

* **A6:** Demo live (Geometry/Quantum/Boundary).

* **A7:** Casebook & packs w marketplace.

* **A8:** Canary→progressive (5→25→100%), post‑mortem & roadmap 2.1.

---

## **3\) Testy – „sami tworzą” (bez Twojej ingerencji)**

**Reguła:** każdy agent ma **Test Charter** i **Definition‑of‑Done** testowe:

* **A1–A4 (silnik):** unit ≥ 85%, property‑based (inwarianty), fuzz dla PNIP/PCO parsingu, contract tests pod OpenAPI, metryki gate’ów karmione realnie.

* **A5 (pipeline):** e2e Smoke (publishable → PCO), Proof‑Only negative, Boundary reconstruct idempotent, ledger merkle‑proof verify.

* **A6 (UX/ops):** testy dostępności (a11y), lighthouse/perf, e2e w Playwright/Cypress z artefaktem PCO.

* **A7 (packs/devices):** scenariusze domenowe (LEX/FIN) – PCO zgodne z rozszerzeniami; Devices: idempotent/retry tests.

* **A8 (SRE/sec):** chaos tests (DR drills), supply‑chain policy tests, rate‑limit & load‑shedding scenariusze.

**Kryterium tygodnia:** każda nowa funkcja → **co najmniej 1 unit \+ 1 integration/contract \+ 1 e2e**, pokrycie i metryki raportowane w PR (CODEX generuje, ale agent przegląda i domyka).

---

## **4\) Zasady integracji (żeby się nie blokować)**

* **Merge okno (środa 16‑18)**: kolejność A5→A1→A2→A3→A4→A7→A6→A8; konflikt \= rebase lokalny.

* **„Green Week Gate” (piątek 12:00 freeze):** wszystkie bramki zielone, zero TODO w PCO, demo 10′, link w `worklog.md`.

* **Konflikty schematów:** jedynym edytorem `schemas/*` jest **A5** (PR’y z innych agentów idą przez A5).

* **Manifest & README:** zmiany centralne – właściciel sekcji; reszta PR → komentarz referencyjny, bez bezpośrednich edycji.

---

## **5\) KPI tygodniowe (dla każdego agenta)**

* **Gate’y:** Gauge ≤ 1e‑3 · Coverage ≥ 0.90 · Δbits \== 0 · Proof‑Only egzekwowane.

* **Perf:** p95 API \< 250 ms (CFE/QTMP/lexqft krytyczne), Cockpit TTI \< 1.5 s.

* **Stabilność:** 0 P1 / ≤1 P2, DR drill zaliczony (gdy zaplanowany).

* **Dowód:** każde demo \= link do Ledger \+ PCO.

