**(cel stanu końcowego) CERTEUS:**

**REPOZYTORIUM \= https://github.com/CERTEUS/certeus.git**

1. Każdy opublikowany artefakt ma **PCO** (Proof‑Carrying Output) z **dowodem machine‑checkable** (LFSC/DRAT/SMT) i **policy snapshotem**.

2. Każdy artefakt ma **proweniencję Merkle** z **dzienną kotwicą** (publiczny log \+ podpis).

3. **SLO‑Gate** blokuje releasy, gdy budżet błędów przekroczony (factuality/calibration/safety/latency/cost).

4. **Verifiable Bench** (publiczne wyniki) bije baseline’y i jest **reprodukowalny offline**.

5. **Zewnętrzny audytor** odtwarza łańcuch dowodowy end‑to‑end bez pytania kogokolwiek o „wytłumaczenie”.

---

## **Skład 10 agentów (stałe role)**

* **A0 – Chief/PM & Architekt**: prowadzi roadmapę, bramki jakości, ryzyka, podpisuje releasy.

* **A1 – PCO & Verifier**: spec PCO, JSON Schema, weryfikator LFSC/DRAT/SMT, CLI `pco`.

* **A2 – Formal Methods**: generacja i walidacja dowodów, cross‑check Z3↔CVC5, certyfikaty UNSAT/SAT.

* **A3 – Provenance/Ledger**: Merkle DAG, membership proofs, kotwice (timestamp/sign), API.

* **A4 – SLO/Observability**: metryki (ECE/Brier/p95), budżety błędów, SLO Gates w CI/CD.

* **A5 – Security/Supply Chain**: SBOM (Syft), skan (Grype), podpisy (cosign), SLSA‑3, sekretologia.

* **A6 – API/Gateway/Policies**: FastAPI, OpenAPI, enforcement proof‑only, OPA/rego.

* **A7 – Cockpit/UI**: PCO Viewer, graf Merkle, „Copy PCO”, śledzenie case’ów.

* **A8 – Bench/Research**: zestawy zadań (PC3/Verus/Dafny \+ domenowe), metodyka i raporty.

* **A9 – QA/Test & Release**: property‑based, metamorphic, fuzz, wydania, dokumentacja release.

**Rytm**: sprint 1‑tygodniowy, **pon** plan, **pt** przegląd \+ bramka. **DoD** \= artefakt w repo \+ testy \+ podpis \+ CI zielone \+ wpis do CHANGELOG.

---

## **Fazy (36 tygodni)**

* **Faza I (T1–T6)** – Fundamenty: PCO v0.3, Verifier MVP, szkic Merkle ledger, metryki SLO, SBOM/podpisy, szkielet UI.

* **Faza II (T7–T12)** – Egzekucja: Proof‑only enforcement, cross‑solver, kotwice publiczne, SLO Gates „na ostro”, PCO Viewer, Bench v0.1.

* **Faza III (T13–T18)** – Ujawnianie selektywne, redaction‑as‑policy, metamorphic harness, audytowe ścieżki E2E.

* **Faza IV (T19–T24)** – Skalowanie: rozproszony proof‑cache, ledger HA, streaming, kalibracja, domeny.

* **Faza V (T25–T32)** – „Moonshots”: TEE opcjonalne, re‑producible builds, multi‑tenant, weryfikatory krzyżowe.

* **Faza VI (T33–T36)** – Pre‑GA → GA: hardening, bug‑bash, audyt zewnętrzny, publiczny raport.

---

## **Twarde bramki jakości (gilotyny)**

* **G1 (koniec T6)**: 90% ścieżek wymaga PCO, `pco verify --strict` ≤ **200 ms**/artefakt offline, 100% deterministycznie.

* **G2 (koniec T12)**: **Kotwica dzienna** aktywna, **SLO‑Gate** blokuje release’y, Bench v0.1 online.

* **G3 (koniec T18)**: Selekt. ujawnianie (Merkle branch proofs) gotowe, **redaction policy** enforce w runtime.

* **G4 (koniec T24)**: Ledger HA, proof‑cache rozproszony, p95 publikacji PCO ≤ **1.2 s**.

* **G5 (koniec T32)**: Reproducible builds, podpisane artefakty, multi‑tenant izolacja.

* **GA (koniec T36)**: Audytor zewnętrzny odtwarza losowy case **bez pytań**, publiczny raport z hashami/PCO.

---

## **Plan tygodniowy – konkrety per tydzień i agent (T1–T12 w pełnej rozdzielczości)**

**Legenda DoD** (Definition of Done): kod \+ testy \+ dokument \+ wpis do `docs/` \+ CI \+ podpis/cosign \+ CHANGELOG.

### **Tydzień 1**

* **A0**: Plan Fazy I, RACI, kalendarz bramek; DoD: `docs/roadmap.md`, `docs/raci.md`.

* **A1**: Szkic **PCO v0.3** (JSON Schema) \+ przykładowy PCO; DoD: `schemas/pco-v0.3.json`, `examples/pco/hello.json`.

* **A2**: Wybór formatu dowodów: **LFSC/DRAT** \+ minimalny checker; DoD: `core/proofs/checkers/README.md`.

* **A3**: Prototyp **Merkle DAG** (hash‑first) – CLI `merkle add/list`; DoD: `tools/merkle/`.

* **A4**: Spis metryk: **ECE, Brier, factuality%, p95/p99**, budżety; DoD: `docs/slo/metrics.md`.

* **A5**: **SBOM** w CI (Syft) \+ skan (Grype); DoD: GH Actions \+ `security/sbom/`.

* **A6**: Szkic **OpenAPI** \+ endpoint `/pco/verify`; DoD: `docs/api/openapi.yaml` \+ stub.

* **A7**: Cockpit skeleton \+ widok „PCO details”; DoD: `services/cockpit/` \+ route.

* **A8**: Zbiór **bench candidates** (PC3/Dafny/Verus \+ domenowe); DoD: `bench/README.md`.

* **A9**: **Property‑based test harness** (Hypothesis) dla PCO; DoD: `tests/property/test_pco.py`.

### **Tydzień 2**

* **A0**: Polityka wersjonowania PCO i polityk; DoD: `policies/VERSIONING.md`.

* **A1**: `pco verify` (CLI) – walidacja schema \+ sygnatury; DoD: `tools/pco/verify.py` \+ tests.

* **A2**: Integracja **Z3** \+ weryfikacja UNSAT → DRAT export; DoD: `core/proofs/z3_bridge.py`.

* **A3**: **Membership proofs** (Merkle): generowanie/verify; DoD: `tools/merkle/prove.py`.

* **A4**: Export metryk do Prometheus; DoD: `monitoring/exporter.py`, `charts/`.

* **A5**: **cosign attest** dla kontenerów; DoD: GH Actions \+ podpisany obraz.

* **A6**: `STRICT_PROOF_ONLY=1` – szkic middleware; DoD: `services/api_gateway/mw_proof_only.py`.

* **A7**: UI: **Copy PCO**, badge „Verified”; DoD: komponent \+ testy UI.

* **A8**: Metodyka Bench v0.1 (seed, RNG, determinism); DoD: `bench/METHOD.md`.

* **A9**: **Metamorphic tests** szkic (perturbacje promptów); DoD: `tests/metamorphic/`.

### **Tydzień 3**

* **A0**: Ryzyka top‑10 \+ mitigacje; DoD: `docs/risks.md`.

* **A1**: PCO: **policy binding** (snapshot ID) \+ `additionalProperties:false`; DoD: schema \+ tests.

* **A2**: **Cross‑check** Z3↔CVC5 na próbkach; DoD: `tests/formal/crosscheck_test.py`.

* **A3**: **Anchor format** (manifest dzienny) – draft; DoD: `ledger/anchor/format.md`.

* **A4**: **SLO budżety** YAML (prog thresholds); DoD: `monitoring/slo.yaml`.

* **A5**: **gitleaks** \+ sekretologia (doprecyz. reguł); DoD: `gitleaks.toml` updated.

* **A6**: OpenAPI lint (`spectral`) \+ error model; DoD: `spectral.yaml` \+ tests.

* **A7**: UI: graf Merkle dla artefaktu; DoD: `components/MerkleGraph`.

* **A8**: Skrypty konwersji zadań Dafny/Verus do formatu bench; DoD: `bench/converters/`.

* **A9**: Fuzz dla API `/pco/verify`; DoD: `tests/fuzz/api_pco_fuzz.py`.

### **Tydzień 4**

* **A0**: **Przegląd G1‑pre**; DoD: notatka z akcji korygujących.

* **A1**: PCO: **outputs\_digest / inputs\_digest** (sha‑256) \+ model\_fingerprint; DoD: schema \+ lib.

* **A2**: **Proof normalizer** (DRAT trim \+ LFSC recheck); DoD: `core/proofs/normalize.py`.

* **A3**: **API Ledger**: `/ledger/add`, `/ledger/proof`; DoD: `services/ledger/`.

* **A4**: **p95/p99** instrumentacja; DoD: dashboard Grafana.

* **A5**: **SLSA‑3** plan \+ artifacts; DoD: `security/slsa/plan.md`.

* **A6**: **OPA/rego**: redaction v0; DoD: `policies/rego/redaction.rego`.

* **A7**: UI: widok **Policy Snapshot**; DoD: `PolicyBadge`.

* **A8**: Bench: pipeline uruchomieniowy; DoD: `bench/run.py`.

* **A9**: **Contract tests** dla OpenAPI (schemathesis); DoD: `tests/contract/`.

### **Tydzień 5**

* **A0**: Governance decyzji (ADR templates); DoD: `docs/adr/0001-template.md`.

* **A1**: PCO: **signatures\[\]** Ed25519 \+ `cosign verify-attestation`; DoD: integracja.

* **A2**: **Differential testing**: solver disagreement alert; DoD: monitor \+ test.

* **A3**: **Kotwica dzienna** – podpis manifestu \+ publikacja; DoD: `ledger/anchor/publish.py`.

* **A4**: **ECE/Brier** kalkulator \+ export; DoD: `monitoring/calibration.py`.

* **A5**: **Repro flags**: `PYTHONHASHSEED=0`, `TZ=UTC`; DoD: Dockerfiles updated.

* **A6**: **Proof‑only** enforcement w 90% ścieżek; DoD: middleware \+ tests.

* **A7**: UI: **Download PCO** \+ **Download Proof**; DoD: przyciski \+ e2e test.

* **A8**: Bench: walidacja deterministyczności; DoD: raport.

* **A9**: **E2E smoke** pipeline (nightly); DoD: GH Actions „nightly‑e2e”.

### **Tydzień 6 – Bramka G1**

* **A0**: Audyt G1; DoD: raport G1 (pass/fail).

* **A1**: Optymalizacja `pco verify` ≤ 200 ms; DoD: profiling \+ wynik.

* **A2**: 100 próbek cross‑check; DoD: tabela wyników \+ flaki.

* **A3**: Proofs: Merkle‑leaf 1:1 z PCO; DoD: złączenie API.

* **A4**: SLO baseline; DoD: dashboard v0.

* **A5**: SBOM w release‑artefaktach; DoD: artefakty w GHCR.

* **A6**: OpenAPI examples z błędami proof‑required; DoD: `docs/api/examples/`.

* **A7**: Cockpit: lista ostatnich kotwic; DoD: widok.

* **A8**: Bench v0.1 – 50 casów; DoD: zbiór \+ wyniki.

* **A9**: QA: property/metamorphic coverage raport; DoD: `reports/qa_T6.md`.

**Warunek przejścia G1**: 90% ścieżek *failuje* bez PCO; `pco verify` **≤ 200 ms**; Merkle proofs działają lokalnie.

---

### **Tydzień 7**

* **A0**: Priorytety Fazy II; DoD: roadmapa T7–T12.

* **A1**: PCO: **provenance{}** rozbudowa (narzędzia, wersje, środowisko); DoD: schema \+ lib.

* **A2**: Export **proof certificate** (artefakt podpisany); DoD: `proofs/certs/`.

* **A3**: **Public anchor** (np. transparency log/tag \+ podpis); DoD: pipeline publikacji.

* **A4**: **SLO‑Gate** projekt (gilotyna) – reguły; DoD: `monitoring/gate.rules`.

* **A5**: **COSIGN policy** required w release; DoD: branch protection.

* **A6**: **OPA** enforcement w runtime (redaction blocking); DoD: testy negatywne.

* **A7**: UI: **Merkle Path Viewer**; DoD: tooltipy, copy path.

* **A8**: Bench: definicja metryk domain‑wise; DoD: `bench/metrics.md`.

* **A9**: Fuzz: inputs\_digest kolizje – testy; DoD: raport.

### **Tydzień 8**

* **A0**: Risk burn‑down; DoD: update `risks.md`.

* **A1**: PCO: **verdict** (accept/reject \+ reason codes); DoD: schema \+ mapping.

* **A2**: **Alt‑checker** minimalny (niezależny parser DRAT/LFSC); DoD: `core/proofs/minchecker/`.

* **A3**: **Membership API** w Cockpit; DoD: `/proof/membership`.

* **A4**: **SLO Gate** w CI (canary); DoD: GH Action `gate.yml`.

* **A5**: **Dependency pinning** (uv.lock) enforce; DoD: policy check.

* **A6**: **Error model** API stabilny (kody błędów); DoD: doc \+ tests.

* **A7**: UI: **PCO diff** (v0.3→v0.3+); DoD: komponent porównawczy.

* **A8**: Bench: **seeded run** \+ CSV; DoD: `bench/results/`.

* **A9**: **Contract chaos** (api breakage detection); DoD: test pipeline.

### **Tydzień 9**

* **A0**: Przegląd SLO Gate na danych; DoD: decyzje progów.

* **A1**: **Selective disclosure map** (które gałęzie ujawniamy komu); DoD: `docs/disclosure.md`.

* **A2**: **Timeout/Resource guards** dla solverów; DoD: sandbox.

* **A3**: **Anchor rotation** i archiwizacja; DoD: polityka.

* **A4**: **Calibration jobs** (ECE/Brier nocne); DoD: cron \+ raport.

* **A5**: **Secrets rotation** \+ KMS; DoD: playbook.

* **A6**: **Proof cache** API (GET/PUT by digest); DoD: `services/proof_cache/`.

* **A7**: UI: **Timeline case’a** (od promptu do proof); DoD: widok.

* **A8**: Bench: baseline vs nasze wyniki; DoD: raport porównawczy.

* **A9**: QA: **mutacja semantyczna** testów; DoD: mutator \+ wyniki.

### **Tydzień 10**

* **A0**: Gate rehearsal (symulacja blokady release’u); DoD: log \+ lessons.

* **A1**: **PCO Validator** jako lib (Python/TS); DoD: `libs/pco/`.

* **A2**: **Witness shrinking** (minimalny dowód); DoD: algorytm \+ test.

* **A3**: **Proof Bundle** (PCO+proof+merkle) – format paczki; DoD: spec \+ impl.

* **A4**: **Cost SLO** ($/req) i budżety; DoD: metryka.

* **A5**: **Repro build**: deterministyczne obrazy; DoD: docker \+ test.

* **A6**: **Quotas** na brak PCO (0% prod); DoD: enforce.

* **A7**: UI: **One‑click audit pack** (zip paczki); DoD: przycisk.

* **A8**: Bench: domena \#2 (np. cytacje/fakty); DoD: nowy set.

* **A9**: **Stress/perf** testy (p95 ≤ 1.5 s); DoD: raport.

### **Tydzień 11**

* **A0**: Dry‑run G2; DoD: lista braków.

* **A1**: **Schema freeze** v0.3; DoD: tag \+ migrator.

* **A2**: **Adversarial set** solverów; DoD: katalog przypadków.

* **A3**: **Public index** ostatnich 30 kotwic; DoD: endpoint \+ UI.

* **A4**: **Gate dashboard** (zielony/czerwony); DoD: panel.

* **A5**: **SBOM diff** między releasami; DoD: narzędzie.

* **A6**: **OPA deny‑by‑default** ścieżki wrażliwe; DoD: testy negatywne.

* **A7**: UI: **Accessibility** \+ dark mode; DoD: checklista.

* **A8**: **Report template** (publiczny PDF/HTML); DoD: `reports/template/`.

* **A9**: **Release checklist** v1; DoD: `RELEASE.md`.

### **Tydzień 12 – Bramka G2**

* **A0**: Audyt G2; DoD: raport G2.

* **A1**: PCO \+ validator – stabilne; DoD: publish libs.

* **A2**: Cross‑check – fail rate \< **0.5%**; DoD: wykres.

* **A3**: Kotwica dzienna – publiczna; DoD: hash log \+ podpis.

* **A4**: **SLO‑Gate aktywny** – blokuje przy naruszeniu; DoD: dowód blokady.

* **A5**: Release z **cosign attest** \+ SBOM; DoD: artefakty.

* **A6**: Proof‑only enforcement 100% publikacji; DoD: logi.

* **A7**: Cockpit: pełen flow; DoD: demo.

* **A8**: Bench v0.1 – wyniki publiczne; DoD: link \+ CSV.

* **A9**: QA: raport T12; DoD: `reports/qa_T12.md`.

**Warunek przejścia G2**: publiczna **kotwica** działa, **SLO‑Gate** realnie blokuje releasy, wyniki Bench opublikowane.

---

## **T13–T36 (skrótowo, ale konkretnie — prace równoległe tydzień po tygodniu)**

Poniżej **oś tygodniowa** z kluczowym celem tygodnia i zadaniami równoległymi; każdy agent realizuje wskazany blok. Szczegóły DoD \= jak powyżej (kod \+ test \+ doc \+ CI \+ podpis).

### **T13 – Selekt. ujawnianie v1**

* A1: PCO **disclosure policy** w schema.

* A2: **Proof slicing** (gałęzie dowodu).

* A3: **Merkle branch proofs** API.

* A4: Metryka **privacy‑leak** (0 incydentów).

* A5: **PII redaction** testy E2E.

* A6: **Policy snapshot** wersjonowanie.

* A7: UI: wybór gałęzi ujawnienia.

* A8: Bench: case’y „partial disclosure”.

* A9: QA: analiza zagrożeń (threat model).

### **T14 – Redaction‑as‑policy**

* A1: PCO `redactions[]`.

* A2: Dowody niełamliwe przy redakcji.

* A3: Proof‑bundle z czerwonymi polami.

* A4: SLO: false‑negative redaction \< **0.1%**.

* A5: DPIA dokument.

* A6: Enforcement „pre‑publish”.

* A7: UI: podgląd redakcji.

* A8: Bench: privacy set.

* A9: Pentest wycieków.

### **T15 – Metamorphic harness v2**

* A1: PCO stability checks.

* A2: Solver invariants (ekwiwalencja).

* A3: Ledger invariants (root stability).

* A4: Drzewa decyzji Gate vs perturbacje.

* A5: Supply‑chain chaos (rollback test).

* A6: API rate limits \+ backpressure.

* A7: UI: „audit trail” ze zmianami.

* A8: Bench: metamorphic scoring.

* A9: Fail‑injection E2E.

### **T16 – Audyt ścieżek E2E**

* A1/A2/A3: „silver path” audytowy: prompt→PCO→proof→ledger→anchor.

* A4: Raport audytowy automatyczny.

* A5: Signed **audit pack**.

* A6: `/audit/download`.

* A7: UI: „Audit this case”.

* A8: Public sample case.

* A9: QA: zgodność offline.

### **T17 – Factuality++ / Kalibracja++**

* A1: PCO: **claim‑units** (sub‑sentence alignment).

* A2: Dowód na poziomie claim‑unit.

* A3: `merkle` liście per claim.

* A4: ECE ≤ **0.02**, Brier ≤ **0.1**.

* A5: alerty kalibracji.

* A6: `/claims` API.

* A7: UI: „support map”.

* A8: Bench: citation/domain set.

* A9: Regression wall.

### **T18 – Bramka G3 – Selekt. ujawnianie \+ redaction w prod**

* A0: audyt G3 i akcept.

* Reszta: dostarcza finalne raporty/artefakty.

### **T19 – Skalowanie: proof‑cache**

* A1: PCO deduplikacja.

* A2: Proof canonicalization.

* A3: Cache rozproszony (Redis/KeyDB \+ digest).

* A4: p95 publikacji ≤ **1.2 s**.

* A5: rate‑limit ataki.

* A6: ETags i 304\.

* A7: UI: cache hits.

* A8: Load bench.

* A9: Soak test 24h.

### **T20 – Ledger HA**

* A1: PCO ids globalne.

* A2: Dowody kompaktowe.

* A3: Ledger replika \+ snapshoty.

* A4: RTO/RPO cele.

* A5: backup polityczny.

* A6: Health endpoints.

* A7: UI: status ledger.

* A8: Failover bench.

* A9: DR test.

### **T21 – Streaming & Telemetria**

* A1: Streaming PCO events.

* A2: Streaming proofs (chunking).

* A3: Event bus \+ podpisy.

* A4: SLO na strumieniach.

* A5: TLS mTLS.

* A6: SSE/WS API.

* A7: UI: live audit.

* A8: Bench strumieniowy.

* A9: Latency/HA tests.

### **T22 – Domeny \#3/\#4**

* A1–A2: profile dowodów dla nowych domen.

* A3: schemat Merkle rozszerzony.

* A4: SLO per‑domain.

* A5: polityki PII per‑domain.

* A6: API namespacing.

* A7: UI filtry domen.

* A8: Bench rozszerzony.

* A9: Domain regression.

### **T23 – Twarde limity i koszty**

* A4: Gate na koszcie; p99 koszt ≤ budżet.

* A5: limity zużycia.

* Inni: optymalizacje.

### **T24 – Bramka G4 – wydajność i HA**

* Weryfikacja p95 ≤ 1.2 s, ledger HA, soak pasuje. Raporty.

### **T25 – Moonshot: TEE (opcjonalnie)**

* A5 prowadzi: zdalna atestacja (SGX/SEV) dla generacji PCO (tryb premium).

* Reszta: integracja ścieżek.

### **T26 – Reproducible builds v1**

* A5/A9: odtwarzalność binarna; deterministyczne pipeline’y.

### **T27 – Multi‑tenant izolacja**

* A6/A5: izolacja tenantów, klucze, polityki.

### **T28 – Weryfikatory krzyżowe (język II)**

* A2: drugi niezależny checker (np. Rust). A1/A9: cross‑lang tests.

### **T29 – Publiczny portal wyników**

* A7/A8: portal Bench z CSV/PCO/anchorami.

### **T30 – Program bug bounty (prywatny)**

* A5/A9: setup, zakres, nagrody, sandbox.

### **T31 – Integracje (np. RAG connectors)**

* A6/A7: integracje zewnętrzne z wymogiem PCO.

### **T32 – Bramka G5 – supply chain & multi‑tenant**

* Audyt łańcucha, multi‑tenant OK, reproducible builds OK.

### **T33 – Pre‑GA Hardening**

* Cały zespół: redukcja długów, performance, doc.

### **T34 – Audyt zewnętrzny (1/2)**

* Audytor dostaje „audit pack”, odtwarza case’y.

### **T35 – Audyt zewnętrzny (2/2) \+ Poprawki**

* Naprawiamy wszystko co wskazał.

### **T36 – GA**

* Publiczny raport: hash kotwic, PCO dla raportu, wyniki Bench, changelog, SBOM, podpisy. Ogłoszenie.

---

## **Artefakty obowiązkowe (stałe DoD)**

* **PCO v0.3**: `schemas/pco-v0.3.json` \+ walidator **Python/TS** \+ `tools/pco/verify`.

* **Proof chain**: `core/proofs/*` (LFSC/DRAT), normalizer, minchecker (drugi niezależny).

* **Merkle ledger**: `services/ledger/*` \+ CLI \+ API \+ anchor publish \+ membership proofs.

* **SLO Gate**: `monitoring/slo.yaml`, `gate.rules`, dashboard \+ blokowanie w CI/CD.

* **Supply chain**: SBOM, Grype, cosign attest, SLSA‑3 dokumentacja.

* **API**: `docs/api/openapi.yaml`, `spectral.yaml`, przykłady błędów `proof-required`.

* **Cockpit**: PCO Viewer, MerkleGraph, AuditPack, Timeline.

* **Bench**: `bench/*` \+ wyniki publiczne \+ portal.

* **QA**: property‑based/metamorphic/differential/soak/perf \+ raporty T6/T12/T18/T24/T32/T36.

---

## **KPI końcowe (cel GA)**

* **Factuality (claim‑level machine‑checked)** ≥ **98%** na Bench v1.

* **ECE** ≤ **0.02**, **Brier** ≤ **0.10** (kalibracja).

* **p95 publish‑time** PCO ≤ **1.2 s**; **p99** ≤ **2.0 s**.

* **Cross‑solver disagreement** \< **0.2%** (z automatycznym triage).

* **SLO‑Gate**: 100% wpadek zatrzymanych (0 „przelotów”).

* **Reproducibility**: ≥ **95%** artefaktów binarnie odtwarzalnych.

* **Audit E2E**: 100% case’ów odtwarzalnych offline.

---

## **Ticket szablony (skrót)**

**Story (PCO):**

* *Jako* Gateway chcę wymagać `PCO.signatures[0].alg=Ed25519` i `policy_snapshot_id`, *aby* publikować tylko weryfikowalne artefakty.

* **Acceptance:** `pco verify --strict` PASS, brak `additionalProperties`, test negatywny 403\.

**Story (Ledger):**

* *Jako* Audytor chcę pobrać **membership proof** dla `outputs_digest`, *aby* potwierdzić kotwicę.

* **Acceptance:** `/ledger/proof?digest=...` → ścieżka Merkle, verify PASS.

**Story (SLO Gate):**

* *Jako* Release chcę, aby **gate** blokował, gdy `ECE>0.02` przez 24h.

* **Acceptance:** symulacja: gate czerwony → release FAIL; zielony → PASS.

---

## **Minimalne „moonshoty”, które robią różnicę**

1. **Dual‑checker** (w innym języku) \+ **alt‑solver cross‑check** – *redundancja poznawcza*.

2. **Publiczne kotwice** z podpisem i indeksacją — *audyt bez łaski*.

3. **Selekt. ujawnianie Merkle** — *dowód, nie ekshibicja danych*.

4. **SLO‑Gate** jako *gilotyna* — *nie ma „prawie dobrze”*.

5. **Bench portal** z paczkami PCO/Proof/Merkle — *„dowód, nie opinia”* dla całego świata.

---

## **Mały „starter pack” do wdrożenia w T1 (kopiuj‑wklej)**

**`schemas/pco-v0.3.json` (szkielet)**

`{`  
  `"$schema": "https://json-schema.org/draft/2020-12/schema",`  
  `"$id": "https://certeus/pco-v0.3.json",`  
  `"title": "PCO v0.3",`  
  `"type": "object",`  
  `"additionalProperties": false,`  
  `"required": ["claim_id","scope","inputs_digest","outputs_digest","model_fingerprint","toolchain","policies","proofs","signatures","provenance","verdict"],`  
  `"properties": {`  
    `"claim_id": {"type":"string","pattern":"^[a-f0-9]{16,64}$"},`  
    `"scope": {"type":"string"},`  
    `"inputs_digest": {"type":"string","pattern":"^[a-f0-9]{64}$"},`  
    `"context_digest": {"type":"string","pattern":"^[a-f0-9]{64}$"},`  
    `"outputs_digest": {"type":"string","pattern":"^[a-f0-9]{64}$"},`  
    `"model_fingerprint": {"type":"string"},`  
    `"toolchain": {"type":"object","additionalProperties": false, "properties": {`  
      `"runtime":{"type":"string"}, "version":{"type":"string"}, "flags":{"type":"array","items":{"type":"string"}}`  
    `}},`  
    `"policies": {"type":"array","items":{"type":"object","additionalProperties": false,"properties":{`  
      `"snapshot_id":{"type":"string"}, "hash":{"type":"string","pattern":"^[a-f0-9]{64}$"}`  
    `}}, "minItems": 1},`  
    `"proofs": {"type":"array","items":{"type":"object","additionalProperties": false,"properties":{`  
      `"type":{"enum":["LFSC","DRAT","SMT-CERT"]}, "digest":{"type":"string","pattern":"^[a-f0-9]{64}$"}, "size":{"type":"integer","minimum":1}`  
    `}}, "minItems": 1},`  
    `"signatures": {"type":"array","items":{"type":"object","additionalProperties": false,"properties":{`  
      `"alg":{"enum":["Ed25519"]}, "key_id":{"type":"string"}, "sig":{"type":"string"}`  
    `}}, "minItems": 1},`  
    `"provenance": {"type":"object","additionalProperties": false,"properties":{`  
      `"prompt_digest":{"type":"string","pattern":"^[a-f0-9]{64}$"},`  
      `"tools":{"type":"array","items":{"type":"string"}},`  
      `"env":{"type":"object"},`  
      `"merkle_leaf":{"type":"string","pattern":"^[a-f0-9]{64}$"}`  
    `}},`  
    `"verdict": {"type":"string","enum":["accept","reject"], "description":"Final, machine-checked"}`  
  `}`  
`}`

**CLI szkic `tools/pco/verify.py` (opis):**

* Wejście: ścieżka do pliku PCO \+ opcje `--strict --offline`.

* Sprawdza: schema, `additionalProperties:false`, podpis(y), sumy, istnienie dowodu, **minchecker** LFSC/DRAT, **opcjonalny** cross‑check.

* Wyjście: `0` \= accept, `1` \= reject \+ reason codes.

Wszystkie pliki zgodnie z Twoim **ForgeHeader** (opis, autor, licencja MIT, data UTC).

---

## **Organizacja pracy (prosto i po staremu)**

* **Zasada „szewc”**: każdy merge musi nosić **PCO artefakt** i **podpis**; brak \= odrzut.

* **Spór techniczny**: zapisujemy jako **ADR**; brak ADR \= decyzja tymczasowa na 1 sprint.

* **Język**: polski w doc (PL/EN w kodzie – jak w pliku code\_standard.md oraz w innych dokumentach repo.).

