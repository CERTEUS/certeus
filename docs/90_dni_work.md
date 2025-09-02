# **90 dni — plan dzienny (18 tygodni × 5 dni)**

### **TYDZIEŃ 1 — Uruchomienie bramek jakości i kontraktów**

**D1 (S3/S6)** Cel: CI żyje.

* Skonfigurować `asset‑guard`, `gauge_gate`, `path_coverage`, `boundary_rebuild`.

* DOD: 4 workflowy **zielone** na push/PR; raport w PR.

**D2 (S3/S6)** Cel: Proof‑Only I/O.

* Wymusić middleware PCO (publishable ⇒ **PCO required**).

* DOD: 3 e2e ścieżki kończą się `DROP` bez PCO; log w ProofGate.

**D3 (S3/S5)** Cel: ChatOps/MailOps smoke.

* Komenda `cfe.geodesic` z ChatOps; ingest jednego e‑maila do PFS.

* DOD: PCO z `io.email.*` i `qtm.sequence[]` trafia do Ledger.

**D4 (S2/S1)** Cel: Telemetria bazowa.

* Wystawić `/v1/cfe/curvature` i `/v1/lexqft/coverage` (wartości realne lub stubowane z metrykami).

* DOD: Gate’y czytają realne pola (`kappa_max`, `coverage_gamma`).

**D5 (wszyscy)** Cel: Demo tygodnia.

* 10‑min demo: ingest → analiza → ProofGate → Ledger.

* KPI: 4/4 gate’y zielone, czas end‑to‑end \< 3 min.

---

### **TYDZIEŃ 2 — Boundary & PNIP w praktyce**

**D6 (S3)** Cel: Boundary recon.

* `bulk_reconstruct()` z `delta_bits` i `bits_delta_map`.

* DOD: Gate Boundary‑Rebuild sprawdza `==0` per shard.

**D7 (S3/S6)** Cel: PNIP twarde.

* Walidacja PNIP na wejściu (hash, jurysdykcja, polityka).

* DOD: Złe PNIP ⇒ 400 \+ PCO błędu.

**D8 (S5)** Cel: Cockpit: **Boundary** zakładka.

* Widok shardów, kompresja, „Reconstruct now”.

* DOD: Link do Ledger \+ kotwice czasu.

**D9 (S6)** Cel: Supply‑chain min.

* SBOM, in‑toto, cosign w CI (deny‑by‑default).

* DOD: Artefakty bez attestacji **blokowane**.

**D10 (wszyscy)** Cel: Demo tygodnia.

* Audyt bez zaufania (ledger → boundary → podpisy).

* KPI: p95 API ≤ 300 ms (dev).

---

### **TYDZIEŃ 3 — CFE v0.1 (geodezje, horyzont)**

**D11 (S1)** Geodezyjny dowód (MVP).

* API `/v1/cfe/geodesic`: ścieżka \+ `geodesic_action`.

* DOD: PCO: `cfe.geodesic_action`.

**D12 (S1)** Horyzont zdarzeń dowodowych (MVP).

* API `/v1/cfe/horizon`: `{locked, horizon_mass}`.

* DOD: PCO: `cfe.horizon_mass`, `locked=true` dla próbek.

**D13 (S5)** Cockpit: **Geometry**.

* Heatmapa Ricciego, lensing map, przycisk „lock”.

* DOD: Interaktywny tooltip \+ link do case.

**D14 (S3/S6)** Gate’y → CFE.

* Gauge‑Gate oparty o realne `kappa_max`.

* DOD: próg 1e‑3 egzekwowany na PR.

**D15** Demo tygodnia — Case LEX.

* Geodezyjny dowód \+ lock → publish.

* KPI: 5 min od ingest do publish.

---

### **TYDZIEŃ 4 — QTMP v0.1 (pomiar, nieoznaczoność)**

**D16 (S2)** `qtm.init_case` \+ baza werdyktów.

* DOD: stan |Ψ⟩ zapisany w case‑graph.

**D17 (S2)** `qtm.measure` \+ `qtm.sequence[]`.

* DOD: PCO: `qtm.collapse_event`, `qtm.predistribution[]`.

**D18 (S2/S5)** Komutatory (L vs T).

* API `qtm.commutator`; Cockpit heatmap komutatorów.

* DOD: Raport „uncertainty\_bound.L\_T”.

**D19 (S2/S6)** Dekoherecja.

* Rejestr kanału (`dephasing/depolarizing/damping`).

* DOD: Kolaps logowany do Ledger.

**D20** Demo tygodnia — pomiar w Cockpicie.

* KPI: kolejność `L→T` vs `T→L` zmienia rozkład wyników (wizual).

---

### **TYDZIEŃ 5 — lexqft v0.1 i Gate Path‑Coverage**

**D21 (S2)** Tunelowanie (WKB‑like).

* `/v1/lexqft/tunnel` \+ PCO: `qlaw.tunneling.*`.

* DOD: dwa scenariusze testowe.

**D22 (S2)** Coverage/uncaptured mass.

* `/v1/lexqft/coverage` agreguje ścieżki i masę.

* DOD: Gate `coverage_gamma ≥ 0.90`.

**D23 (S5)** Cockpit: **Quantum**.

* „Operator Composer” (W/I/C/L/T), wykresy.

* DOD: zapis presetów operatorów.

**D24 (S1/S2)** Most CFE↔QTMP.

* Metryki CFE wpływają na priorytety QTMP.

* DOD: korelacja w PCO.

**D25** Demo tygodnia — ścieżki vs pomiar.

---

### **TYDZIEŃ 6 — Devices v0.1**

**D26 (S4/S2)** HDE (Horizon Drive Engine) — plan.

* `/v1/devices/horizon_drive/plan` \+ `plan_of_evidence[]`.

* DOD: budżet `cost_tokens`.

**D27 (S2)** Q‑Oracle — expectation bez kolapsu.

* `/v1/devices/qoracle/expectation`.

* DOD: raport dystrybucji.

**D28 (S2)** Entangler.

* `/v1/devices/entangle` → `target_negativity`.

* DOD: certyfikat PCO.

**D29 (S2/S4)** Chronosync (MVP).

* `/v1/devices/chronosync/reconcile`.

* DOD: szkic klauzul traktatu.

**D30** Demo tygodnia — 4 devices E2E.

---

### **TYDZIEŃ 7 — FINENITH v0.1 (Quantum Alpha)**

**D31 (S4)** Operatory R/S (ryzyko/sentyment).

* DOD: `[R̂,Ŝ] ≠ 0` raportowane.

**D32 (S4)** Splątanie aktywów.

* `fin.entanglement.mi` \+ dashboard.

* DOD: 3 pary aktywów.

**D33 (S4/S5)** Polityki ryzyka.

* Limity, DP/ZK dla sygnałów.

* DOD: 2 polityki w OPA.

**D34 (S4)** API: `alpha/measure` \+ PCO.

* DOD: parametry pomiaru, log.

**D35** Demo tygodnia — **Quantum Alpha**.

---

### **TYDZIEŃ 8 — LEXENITH v0.1**

**D36 (S4)** Micro‑Court/Motion generator.

* DOD: 2 wzorce pism, PCO linki do cytatów.

**D37 (S4)** CLDF/LEX‑FONTARIUS.

* Cytowania z hash, renormalizacja autorytetu.

* DOD: `/cldf/renormalize`.

**D38 (S4)** Why‑Not / PCΔ.

* Eksport kontr‑argumentów.

* DOD: `why_not.trace_uri`.

**D39 (S4/S1)** Horyzont w sprawach.

* Lock / recall / revoke.

* DOD: DR‑Replay/Recall powiązane.

**D40** Demo tygodnia — case wygrany HDE.

---

### **TYDZIEŃ 9 — Security hardening**

**D41 (S6)** PQ‑crypto end‑to‑end.

* Hybryda Ed25519 \+ ML‑DSA, FROST 2‑z‑3.

* DOD: rotacja kluczy wg §26.

Status: Gate PQ‑crypto (stub) dodany do Proof Gate (CI) z flagami `PQCRYPTO_REQUIRE`/`PQCRYPTO_READY`; domyślnie informacyjne, możliwość wymuszenia zielonego.

**D42 (S6)** TEE profil (opcjonalny).

* Attestation w ProofGate.

* DOD: „bunkier” on/off.

Status: Bramki Bunkra (CI) + stub attestation + runbook. ProofGate wymaga `pco.tee.attested=true` przy aktywnym profilu.

**D43 (S6)** OPA/Rego — fine‑grained.

* Role AFV/ASE/ATC/ATS/AVR.

* DOD: enforce publish/merge.

Status: roles.rego + bramka ról (OPA proxy), Governance Pack (lex/fin/sec), walidator spójności oraz enforcement w ProofGate (domena → rola publish); smoke E2E w Proof Gate.

**D44 (S6)** Secret mgmt/DP/MPC.

* Budżet ε w PCO; przepływy MPC.

* DOD: testy wycieku.

Status: Bramki DP budget (stub, `STRICT_DP_BUDGET`) w Proof Gate; gotowe do rozszerzeń testów wycieku.

**D45** Pentest tygodnia (wew.).

---

### **TYDZIEŃ 10 — Observability & SRE**

**D46 (S6)** OTel \+ eBPF \+ profiling.

* DOD: trace z korelacją do PCO.

**D47 (S6)** SLO \+ alerty multi‑burn‑rate.

* p95/p99 \+ error budget.

* DOD: alerty sensowne, niegadatliwe.

**D48 (S6)** DR‑drills.

* Symulacja awarii shardu Boundary.

* DOD: RTO ≤ 30’, RPO ≤ 5’.

**D49 (S6/S3)** Canary/progressive.

* Feature gates \+ rollout.

* DOD: playbook wydania.

**D50** Demo tygodnia — SRE dashboard.

---

### **TYDZIEŃ 11 — Wydajność**

**D51 (S1/S2)** CFE/lexqft tuning.

* Batch windows, pre‑alloc.

* DOD: p95 API ≤ 250 ms (dev).

**D52 (S5)** Cockpit perf.

* Lazy load, pagination, memo.

* DOD: TTI \< 1.5 s.

**D53 (S3)** ProofFS I/O.

* Montaż RO, cache warstwa.

* DOD: \< 20 ms p95 odczytu.

**D54 (S4)** FIN/LEX perf.

* Strumienie (Kafka/Redpanda).

* DOD: backpressure opanowane.

**D55** Mini‑benchmark publiczny (PDF).

---

### **TYDZIEŃ 12 — Compliance & Data Gov**

**D56 (S6)** ISO/SOC2 mapowanie.

* Matryce zgodności → moduły.

* DOD: checklisty audytu.

**D57 (S6)** RODO/DPIA.

* Minimalizacja danych, UPN revoke.

* DOD: ścieżka „prawo do zapomnienia”.

**D58 (S3)** DPCO/MCO.

* Lineage, consent refs, dp\_epsilon.

* DOD: pola w PCO.

**D59 (S3/S5)** Redakcja/maski.

* PFS z polityką redakcji.

* DOD: demo PII‑safe.

**D60** Demo tygodnia — audyt formalny.

---

### **TYDZIEŃ 13 — Devices v0.2**

**D61 (S2)** HDE optymalizacja (koszt/krzywizna).

* DOD: planner porównawczy.

**D62 (S2)** Q‑Oracle heurystyki.

* Uogólnione pytania.

* DOD: API doc.

**D63 (S2)** Entangler scenariusze.

* Multi‑evidence entanglement.

* DOD: metryki negatywności.

**D64 (S2/S4)** Chronosync protokoły.

* Zderzenia doktryn i mediacja.

* DOD: wzorzec klauzul.

**D65** Demo tygodnia — urządzenia 2.0.

---

### **TYDZIEŃ 14 — UX/A11y/i18n/Marketplace**

**D66 (S5)** A11y WCAG 2.2 AA.

* Kontrasty, klawiatura, ARIA.

* DOD: audyt a11y.

**D67 (S5)** i18n PL/EN pełne.

* Ω‑Kernel `lang` transform.

* DOD: testy holonomii językowej.

**D68 (S5)** Marketplace wtyczek.

* Instalacja/upgrade z podpisem.

* DOD: 2 wtyczki demo.

**D69 (S5/S3)** Billing & Cost‑tokens.

* Płatności vs budżet compute.

* DOD: status `PENDING` → allocate.

**D70** Demo tygodnia — sklep wtyczek.

---

### **TYDZIEŃ 15 — Public API & SDK**

**D71 (S3)** OpenAPI domknięte.

* Wersje/compat \+ examples.

* DOD: walidacja kontraktowa.

**D72 (S3)** SDK py/ts/go.

* Publikacje do rejestrów.

* DOD: quickstarts.

**D73 (S5)** DevEx w Cockpicie.

* „Copy code” \+ curl/SDK.

* DOD: 1‑klikowy playground.

**D74 (S6)** Rate‑limits/quotas.

* Token bucket \+ sheds QTMP.

* DOD: testy przeciążeniowe.

**D75** Demo tygodnia — API/SDK day.

---

### **TYDZIEŃ 16 — Piloty zewnętrzne**

**D76 (S4)** Pilot LEX (kancelaria).

* 3 sprawy E2E.

* DOD: feedback \+ metryki.

**D77 (S4)** Pilot FIN (desk trading).

* 2 strategie Q‑Alpha.

* DOD: symulacja \+ PnL raport.

**D78 (S3/S6)** Observability u klienta.

* Exporter \+ dashboards.

* DOD: SLO per tenant.

**D79 (S5)** UX poprawki z pilota.

* Top‑10 pain points.

* DOD: changelog.

**D80** Demo tygodnia — studia przypadków.

---

### **TYDZIEŃ 17 — Go‑to‑Market**

**D81 (S5/S3)** Landing/Demo live.

* Social preview, OG, linki PCO.

* DOD: „Try now” sandbox.

**D82 (S3/S6)** Cennik/limity.

* Proof‑Cost tokens, tiering.

* DOD: polityki billing.

**D83 (S6)** Umowy/compliance.

* DPA, ToS, DP budżety.

* DOD: wzorce do podpisu.

**D84 (S5)** Materiały prasowe.

* One‑pager, deck, wideo 2 min.

* DOD: PR kit.

**D85** „Friends & Family” release.

---

### **TYDZIEŃ 18 — Launch 1.0**

**D86 (wszyscy)** Code freeze \+ RC.

* Gate’y zielone, testy dymne.

* DOD: tag v1.0.0.

**D87 (S6)** Canary → progressive.

* 5% → 25% → 100% ruchu.

* DOD: brak regresji SLO.

**D88 (S5)** Event launch (live).

* Demo: Geometry/Quantum/Boundary.

* DOD: nagranie i linki.

**D89 (S3/S4)** Docs & samples.

* Cookbooki FIN/LEX.

* DOD: repo examples.

**D90 (wszyscy)** Retrospektywa i roadmapa 1.1.

* Zbieramy OKR i priorytety.

* DOD: plan 1.1 (Devices+, SYNAPSY P2P, Med/Sec packs).

---

## **Kryteria „Każdy dzień na zielono” (checklist)**

* **Gate’y CI**: Gauge ≤ 1e‑3 · Coverage ≥ 0.90 · Boundary Δbits \== 0\.

* **PCO**: każda publikowalna odpowiedź zawiera PCO i rozszerzenia domeny.

* **SLO dev**: p95 ≤ 300 ms (docelowo 250\) · error‑budget OK.

* **Artefakty**: SBOM \+ in‑toto \+ cosign; brak → blokada.

* **Demo dnia**: Nowa funkcja widoczna w Cockpicie \+ link do Ledger.

---

## **Co jeszcze „ponad Big Tech”**

* **Fizyka sensu jako inwariant** (Ω‑Kernel) zamiast heurystyk.

* **Boundary (holograficzny brzeg)** — pełny audyt bez zaufania.

* **Devices** (HDE/Q‑Oracle/Entangler/Chronosync) — *maszyny* nad prawem i finansami.

* **Proof‑Only I/O** — publikacja bez PCO jest niemożliwa technicznie.

* **QTMP** — kolaps i nieoznaczoność jako pierwszoklasowe obywatele API.
