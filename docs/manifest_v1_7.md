# ┌──────────────────────────────────────────────────────────────┐

# │                           CERTEUS                           │

# │            Proof‑native AI for Law • Evidence OS            │

# └──────────────────────────────────────────────────────────────┘

# **Manifest Jednolity v1.7 (R&D / DRAFT)**

> Uwaga: dokument badawczy. Źródłem prawdy pozostaje `docs/manifest.md` (v1.5 Immutable).

**Opis (PL):** Kanoniczny manifest systemu CERTEUS, gotowy „pod ukończenie”. Zawiera normy (MUST/SHOULD), kontrakt publikacji (PCO), schemat **ProofBundle v0.2**, progi **SLO‑Gate**, zasady **Law‑as‑Data**, redakcję PII, zgodność **AI Act/RODO**, reprodukowalność, bezpieczeństwo, API i Definition of Done.  
**Description (EN):** Canonical CERTEUS manifest, release‑ready. Includes RFC2119 terms, PCO publication contract, **ProofBundle v0.2** schema, **SLO‑Gate** thresholds, **Law‑as‑Data** rules, PII redaction, **AI Act/GDPR** compliance, reproducibility, security, APIs, and Definition of Done.

**Plik | File:** `docs/manifest.md`  
**Autor | Author:** Radosław Skarżycki (Radziu)  
**Wersja | Version:** 1.7  
**Data | Date:** 2025‑08‑31T00:00:00Z  
**Licencja | License:** MIT  
**Repo:** CERTEUS  
**Status:** **Immutable Core** (zmiany tylko poprzez inkrement wersji)

> **Motto:** *Dowód, nie opinia.*  
> **Zasada rdzenia:** Rdzeń jest **niezmienialny** (PCO/Boundary/ProofGate/Truth Engine). Wszystko inne to **wtyczki** i **polityki**.

---

## 0) RFC2119 – słowa mocy

**MUST/SHALL** = bezwzględnie Wymagane; **SHOULD** = zalecane (odchylenie wymaga uzasadnienia); **MAY** = opcjonalne.

---

## 1) Cel i zakres

System **proof‑native** do tworzenia, weryfikacji i publikacji artefaktów dowodowych dla pism i decyzji prawnych. Rdzeń obejmuje: **Truth Engine**, **ProofGate**, **PCO‑Ledger**, **Boundary**. Manifest określa *normy produktu*, nie marketing.

---

## 2) Architektura – rdzeń i szyny

- **Truth Engine (TE)** — formalizacja tez i wniosków; modele decyzyjne z kontrolą niepewności.
- **ProofGate (PG)** — jedyna brama publikacyjna; egzekwuje polityki **PCO** i **SLO‑Gate**.
- **PCO‑Ledger** — finalność wpisów, **Merkle‑root**, podpisy **Ed25519**; payload publiczny bez PII.
- **Boundary** — granica domenowa (compliance, redakcja PII, law‑as‑data, audyt, klucze, JWKS).
- **Continuity/Context Forge (cfpack)** — deterministyczne pakiety kontekstu; **Domain Packs** (prawo/finanse/kod/sec/med).
- **Fizyka sensu** (*CFE/lexqft/QTMP*) — warstwa modelowa; *tu jedynie interfejsy i artefakty, bez metafizyki*.

> **Absolut:** Każdy artefakt, który przechodzi przez ProofGate, musi być ujęty w **ProofBundle** i podlegać polityce **PCO**.

---

## 3) Kontrakt publikacyjny (PCO)

**Jedyny wynik publikacji:** `PUBLISH | CONDITIONAL | PENDING | ABSTAIN`.

### 3.1 Progi i checki (normatyw)

- **Ryzyko (MUST):** `ece ≤ 0.02`, `brier ≤ 0.10`, `abstain_rate ≤ 0.15`, `p95_latency_ms` raportowane.
- **Weryfikacja dowodów (MUST):** każdy dowód SMT/LFSC/DRAT zweryfikowany narzędziem referencyjnym.
- **Źródła (MUST):** każdy cytat prawa/orzeczenia posiada `digest` (SHA256/Blake3), `retrieved_at`, **cache offline**.
- **Podpis (MUST):** rola `counsel` podpisuje bundle przy `PUBLISH/CONDITIONAL`.
- **Abstain (MUST):** jeżeli którykolwiek warunek krytyczny nie spełniony ⇒ `ABSTAIN` (fail‑closed).

### 3.2 Policy Pack (plik)

`policies/pco/policy_pack.yaml` — patrz Aneks A (normatywny skeleton dołączony).

---

## 4) ProofBundle v0.2 — norma

**Cel:** Jeden, sądownie strawny pakiet dowodowy dołączany do pisma.

**Ścieżka schematu (MUST):** `services/api_gateway/schemas/proofbundle_v0.2.json`  
**Endpoint (MUST):** `POST /v1/pco/bundle` ⇒ zwraca podpisany **ProofBundle** (Ed25519), wpis do `PCO‑Ledger`.  
**Publiczny odczyt (MUST):** `GET /pco/public/{case_id}` ⇒ payload bez PII, JWKS pod `/.well-known/jwks.json`.

### 4.1 Wymagane pola (normatyw)

```
version:\"0.2\", case_id, created_at, jurisdiction{country,domain},
claims[{id,text,legal_basis{statutes[],cases[]},evidence_refs[]}],
sources[{id,uri,digest,retrieved_at,license?}],
derivations[{claim_id,solver(z3|cvc5|other),proof_format(DRAT|LRAT|LFSC|AIGER|OTHER),artifact_digest,verifier_cmd?}],
computations[{name,artifact_digest,notebook_cells?}],
risk{ece,brier,p95_latency_ms,abstain_rate},
ledger{pco_tx_id?,merkle_root?},
signatures[{role(producer|auditor|counsel|court|insurer),alg(ed25519|p256|p384|rsa),key_id,signature}],
reproducibility{image,image_digest,seed,env},
attachments[{name,mime,digest}],
status(PUBLISH|CONDITIONAL|PENDING|ABSTAIN)
```

Pełny JSON Schema — **Aneks B**.

### 4.2 Zasady

- **Deterministyczność (MUST):** `image_digest` + `seed` + jawne `env` zapewniają powtarzalny wynik (hash‑lock).
- **Spójność (MUST):** każdy `claim` musi wskazywać podstawy prawne i dowody/wywody (`derivations`).
- **Odtwarzalność (MUST):** `verifier_cmd` lub dokumentacja kroku weryfikacji dla proofów.

---

## 5) Law‑as‑Data — norma cytowań

- **Digest (MUST):** każda ustawa, rozporządzenie, orzeczenie, komentarz — `digest = SHA256|Blake3` + `retrieved_at`.
- **Cache (MUST):** lokalny cache `storage/law/{digest}`; publikacja bez PII i bez ograniczeń licencyjnych.
- **Zakaz (MUST):** brak „gołych linków” w ProofBundle (linki tylko jako metadane DoDatkowe).
- **wersjonowanie (SHOULD):** mapowanie `Dz.U./LEX/curia` → digest + zakres obowiązywania w czasie.

---

## 6) Redakcja PII i prywatność

- **Tryb public payload (MUST):** PII usunięte lub zanonimizowane; polityka `policies/pco/policy_pack.yaml:redaction`.
- **Role RODO (MUST):** `controller = Kancelaria/Client`, `processor = CERTEUS`.
- **Retencja (MUST):** `public_payload_days = 3650`, `private_artifacts_days = 3650`.

---

## 7) Zgodność – AI Act (UE) i RODO

- **Klasa ryzyka (MUST):** zastosowania w wymiarze sprawiedliwości ⇒ *high‑risk*.
- **Wymogi (MUST):** data governance, traceability, logging, human oversight (counsel), robustness, accuracy (SLO‑Gate).
- **DPIA (SHOULD):** ocena skutków dla ochrony danych.

---

## 8) Reproducibility & Supply Chain

- **SBOM/SLSA (SHOULD):** generowane w CI; attestations podpisane.
- **Obrazy (MUST):** publikacja `image` + `image_digest` (OCI); blokada wykonania mieszanki buildów.

---

## 9) Bezpieczeństwo

- **Podpisy (MUST):** `Ed25519` + **JWKS** (`/.well-known/jwks.json`).
- **Sekrety (MUST):** KMS/Vault; brak sekretów w repo.
- **Headers (SHOULD):** CSP/HSTS; rate‑limit; mTLS dla usług wewnętrznych.

---

## 10) Observability & SLO‑Gate

- **Metryki (MUST):** `certeus_ece`, `certeus_brier`, `certeus_abstain_rate`, `certeus_compile_duration_ms_bucket`, `verification_failed_total`, `source_fetch_errors_total`.
- **Alerty (MUST):** krytyk przy `verification_failed_total>0`.
- **Progi (MUST):** `ece≤0.02`, `brier≤0.10`, `abstain_rate≤0.15` — patrz **Aneks C** (Prometheus rules).

---

## 11) API – powierzchnia minimalna

- `POST /v1/pco/bundle` — tworzy i publikuje ProofBundle.
- `GET /pco/public/{case_id}` — zwraca public payload ProofBundle.
- `GET /.well-known/jwks.json` — klucze publiczne.
*(OpenAPI: `docs/openapi/certeus.v1.yaml`, MUST zawierać schematy ProofBundle i przykłady odpowiedzi.)*

---

## 12) Przepływ E2E (normatyw)

1. **Ingest** źródeł i faktów → cache + digest.
2. **Claims** + **legal_basis** + **derivations** (SMT/LFSC) → weryfikacja.
3. **ProofBundle** z metrykami ryzyka i podpisami.
4. **ProofGate/PCO**: decyzja (`PUBLISH/…/ABSTAIN`).
5. **Ledger**: wpis, Merkle, JWKS.
6. **Załącznik do pisma**: ProofBundle jako **Annex**.

---

## 13) Role i odpowiedzialność

- **Producer** — generuje bundle; **Auditor** — weryfikuje; **Counsel** — nadzór ludzki, podpis; **Court/Insurer** — opcjonalne podpisy.

---

## 14) Retencja i dostęp

- Zgodnie z Policy Pack; dostęp do prywatnych artefaktów ograniczony; public payload nie zawiera PII.

---

## 15) Release & wersjonowanie

- **Immutable**: każda zmiana = nowa Wersja manifestu i schematów.
- **Tagi:** `vX.Y` + hash; CHANGELOG z odnośnikiem do Merkle‑root.

---

## 16) Definition of Done (DoD) - "ukończenie systemu"

**A. KOD i SCHEMATY** (MUST)

- [ ] `services/api_gateway/schemas/proofbundle_v0.2.json` zgodny z Aneksem B.
- [ ] Endpointy `/v1/pco/bundle`, `/pco/public/{case_id}`, `/.well-known/jwks.json` (testy e2e).
- [ ] `policies/pco/policy_pack.yaml` jak w Anekście A (progi PCO, redakcja, role).
- [ ] `monitoring/slo/slo_gate.yml` jak w Anekście C (reguły i bramki).
- [ ] Moduł **Law-as-Data**: cache + digest + adaptery.

---

## 17) Smoke & E2E

**Cel (MUST):** Każda zmiana przechodzi szybki, przekrojowy test działania API (smoke) oraz e2e w pytest, z twardym raportowaniem błędów i SLO (p95).

- Lokalne uruchomienie (Windows):
  - `. .\scripts\dev_env.ps1`; `pwsh -File .\scripts\smoke_api.ps1`
- Lokalne uruchomienie (Linux/macOS):
  - `source ./scripts/dev_env.sh`; `bash ./scripts/smoke_api.sh`
- CI (GitHub Actions):
  - Workflow `Smoke` (Ubuntu + Windows) w `.github/workflows/smoke.yml` – tworzy `.venv`, instaluje zależności (z `constraints/requirements-constraints.txt`) i uruchamia skrypty smoke.
- Zakres: health/root/metrics/JWKS, CFE, QTMP, Devices, Ethics, DR, Export, ChatOps, Ledger, Verify, PCO bundle + public verify, Preview (multipart), Ingest/Analyze (PDF), Source cache.
- Raportowanie (MUST):
  - Skrypty smoke drukują listę wyników [OK/ERR] oraz podsumowanie: `total`, `passes`, `fails`, `p95_ms`.
  - `p95_ms` liczony na podstawie histogramu Prometheus `certeus_http_request_duration_ms_bucket` z `/metrics` (sumarycznie dla całego smoke).
- Kryterium: jakikolwiek błąd -> exit code != 0 (fail CI). p95 buduje się z histogramu startującego od zera (serwer startuje świeżo w smoke).

**B. OBSERVABILITY/SECURITY** (MUST)

- [ ] Metryki + alerty krytyczne; dashboard.
- [ ] JWKS żywe; klucze w KMS/Vault; polityka rotacji.

**C. COMPLIANCE** (MUST)

- [ ] Matryca AI Act (high‑risk) + DPIA.
- [ ] Procedura `ABSTAIN` + ścieżka eskalacji do Counsel.

**D. REPRODUCIBILITY** (MUST)

- [ ] SBOM/SLSA; `image_digest` + `seed`.

**E. QA** (MUST)

- [ ] 0 krytycznych; 100% przejścia bramek PCO/SLO.

---

## 17) Glosariusz (skróty)

**PCO** — Publication Contract & Observability. **ProofBundle** — pakiet dowodowy. **JWKS** — JSON Web Key Set. **ECE/Brier** — metryki kalibracji. **ABSTAIN** — bezpieczne wstrzymanie.

---

## Aneks A — PCO Policy Pack (skeleton, normatywny)

```yaml
meta:
  id: pco-policy-pack
  version: "0.1"
  jurisdiction: "PL"
  tags: [ai_act:high_risk, rodo, legal_ai, proof_native]

publish_contract:
  thresholds:
    risk:
      ece_max: 0.02
      brier_max: 0.10
      abstain_rate_max: 0.15
    reproducibility:
      required: true
      verifier: "certeus-proof-verifier>=0.2"
    sources:
      digest_required: true
      offline_cache_required: true
    proofs:
      formats_allowed: ["DRAT","LRAT","LFSC"]
      solver_allowed: ["z3","cvc5"]
      verification_required: true

checks:
  - id: sources_digest
    description: "Każde źródło posiada digest i retrieved_at"
    required: true
  - id: proof_verification
    description: "Wszystkie proofy zweryfikowane narzędziem referencyjnym"
    required: true
  - id: rodo_guard
    description: "Brak PII w payloadzie publicznym"
    required: true
  - id: counsel_signature
    description: "Podpis roli 'counsel' przy PUBLISH/CONDITIONAL"
    required: true

abstain_rules:
  - when: "risk.ece > thresholds.risk.ece_max"
  - when: "risk.brier > thresholds.risk.brier_max"
  - when: "risk.abstain_rate > thresholds.risk.abstain_rate_max"
  - when: "proofs.verification_failed == true"
  - when: "sources.digest_missing > 0"

roles:
  producer: { can_sign: true }
  auditor:  { can_sign: true }
  counsel:  { can_sign: true, required_for: ["PUBLISH","CONDITIONAL"] }

ledger:
  backend: "pco_ledger_v1"
  finalize_after: "2 confirmations"

retention:
  public_payload_days: 3650
  private_artifacts_days: 3650

redaction:
  pii_patterns:
    - "\\bPESEL\\b"
    - "\\b[A-Z]{2}\\d{7}\\b"
  mode: "remove"

compliance:
  rodo: { controller: "Client (law firm)", processor: "CERTEUS" }
  ai_act: { risk_class: "high" }
```

---

## Aneks B — ProofBundle v0.2 (JSON Schema)

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "CERTEUS ProofBundle v0.2",
  "type": "object",
  "required": ["version","case_id","created_at","jurisdiction","claims","sources","risk","signatures","reproducibility","status"],
  "properties": {
    "version": { "type": "string", "const": "0.2" },
    "case_id": { "type": "string", "minLength": 1 },
    "created_at": { "type": "string", "format": "date-time" },
    "jurisdiction": {
      "type": "object",
      "required": ["country","domain"],
      "properties": {
        "country": { "type": "string" },
        "domain":  { "type": "string", "enum": ["civil","criminal","commercial","administrative","labor","other"] }
      }
    },
    "claims": {
      "type": "array", "minItems": 1,
      "items": {"type":"object","required":["id","text","legal_basis"],
        "properties": {
          "id": {"type":"string"},
          "text": {"type":"string"},
          "legal_basis": {"type":"object","required":["statutes","cases"],
            "properties": {
              "statutes": {"type":"array","items":{"type":"string"}},
              "cases": {"type":"array","items":{"type":"string"}}
            }
          },
          "evidence_refs": {"type":"array","items":{"type":"string"}}
        }
      }
    },
    "sources": {"type":"array","items": {"type":"object","required":["id","uri","digest","retrieved_at"],
      "properties": {"id":{"type":"string"},"uri":{"type":"string"},"digest":{"type":"string"},"retrieved_at":{"type":"string","format":"date-time"},"license":{"type":"string"}}}},
    "derivations": {"type":"array","items": {"type":"object","required":["claim_id","solver","proof_format","artifact_digest"],
      "properties": {"claim_id":{"type":"string"},"solver":{"type":"string","enum":["z3","cvc5","other"]},"proof_format":{"type":"string","enum":["DRAT","LRAT","LFSC","AIGER","OTHER"]},"artifact_digest":{"type":"string"},"verifier_cmd":{"type":"string"}}}},
    "computations": {"type":"array","items": {"type":"object","required":["name","artifact_digest"],
      "properties": {"name":{"type":"string"},"artifact_digest":{"type":"string"},"notebook_cells":{"type":"integer"}}}},
    "risk": {"type":"object","required":["ece","brier","p95_latency_ms","abstain_rate"],
      "properties": {"ece":{"type":"number","minimum":0},"brier":{"type":"number","minimum":0},"p95_latency_ms":{"type":"number","minimum":0},"abstain_rate":{"type":"number","minimum":0,"maximum":1}}},
    "ledger": {"type":"object","properties": {"pco_tx_id":{"type":"string"},"merkle_root":{"type":"string"}}},
    "signatures": {"type":"array","minItems":1,
      "items":{"type":"object","required":["role","alg","signature","key_id"],
        "properties": {"role":{"type":"string","enum":["producer","auditor","counsel","court","insurer"]},"alg":{"type":"string","enum":["ed25519","p256","p384","rsa"]},"key_id":{"type":"string"},"signature":{"type":"string"}}}},
    "reproducibility": {"type":"object","required":["image","image_digest","seed"],
      "properties": {"image":{"type":"string"},"image_digest":{"type":"string"},"seed":{"type":"string"},"env":{"type":"object"}}},
    "attachments": {"type":"array","items": {"type":"object","required":["name","mime","digest"],
      "properties": {"name":{"type":"string"},"mime":{"type":"string"},"digest":{"type":"string"}}}},
    "status": { "type":"string","enum":["PUBLISH","CONDITIONAL","PENDING","ABSTAIN"] }
  }
}
```

---

## Aneks C — SLO‑Gate (Prometheus)

```yaml
prometheus_rules:
  groups:
    - name: certeus_slo
      rules:
        - alert: ProofVerificationFailures
          expr: rate(certeus_proof_verification_failed_total[5m]) > 0
          for: 10m
          labels: { severity: "critical" }
          annotations: { summary: "Proof verification failing" }
        - alert: EvidenceLinkRot
          expr: rate(certeus_source_fetch_errors_total[1h]) > 0.05
          for: 2h
          labels: { severity: "warning" }
          annotations: { summary: "Source retrieval/digest mismatch" }
        - alert: HighAbstainRate
          expr: avg_over_time(certeus_abstain_rate[30m]) > 0.15
          for: 30m
          labels: { severity: "warning" }
          annotations: { summary: "Abstain rate exceeded" }
        - record: certeus_compile_p95_ms
          expr: histogram_quantile(0.95, sum(rate(certeus_compile_duration_ms_bucket[5m])) by (le))

gate_decision:
  inputs:
    - { metric: certeus_proof_verification_failed_total, op: "==", value: 0 }
    - { metric: certeus_abstain_rate, op: "<=", value: 0.15 }
    - { metric: certeus_ece, op: "<=", value: 0.02 }
    - { metric: certeus_brier, op: "<=", value: 0.10 }
    - { metric: certeus_sources_digest_missing, op: "==", value: 0 }
  decision:
    if_all_true: "PUBLISH"
    else_if_any_alert_critical: "ABSTAIN"
    else: "CONDITIONAL"
```

