# CERTEUS — Manifest Jednolity **v1.5 (Immutable)**

**Motto:** _Dowód, nie opinia._
**Teza:** rdzeń _niezmienialny_, wszystko inne – _wtyczki_ i _polityki_.

## 0) TL;DR — trafienia w punkt

- **Mikrojądro + proof-native:** Truth Engine, ProofGate, PCO Ledger, Boundary; PNIP/UPN; publikacja **tylko z PCO**.
- **Fizyka sensu:** **CFE** (geometria), **lexqft** (całki po ścieżkach), **QTMP** (pomiar/niepewność).
- **Continuity:** Context Forge (cfpack) + **Domain Packs** (prawo/finanse/kod/sec/med).
- **Interfejsy pierwszej klasy:** **MailOps** (ingest+reply z PCO), **ChatOps** (jedno okno tekstowe sterujące całym systemem, z Proof-Gate).
- **CI/SLO-Gate,** monorepo, API/CLI szkielety, run-time flow.
- **Rozszerzenia:** Equity-Meter + **HHE / Double-Verdict**, ZHG (governance pack), ProofWASM, Why-Not/PCΔ, DR-Replay/Recall, Billing/Cost-tokens, SYNAPSY (P2P).
- **Zjawiska kwantowe (lexqft/QTMP):** tunelowanie, wirtualne pary, renormalizacja autorytetu, SSB zgody — z telemetryką i endpointami.

---

## 1) Aksjomaty i **Ω-Kernel** (Gauge-Invariance of Meaning)

**Zasada Lokalnej Niezmienniczości Sensu:** wynik nie zależy od reprezentacji (język, jurysdykcja, wersja prawa, ontologia).

- **Rejestr transformacji (Ω-Kernel):** `lang`, `jurisdiction`, `revision`, `ontology_map`.
- **Kompensatory (bridges):** automatyczne mapowania; KPI: `gauge.compensators_count`.
- **Gauge-Gate (CI):** test **holonomii** sensu (cykl transformacji) ≤ ε; metryka `gauge.holonomy_drift`.

---

## 2) Architektura i monorepo (docelowy układ)

Warstwy: **Core → Services → Modules → Plugins (Domain Packs) → Clients → Infra**

```
/core/                # TE, PCO SDK, crypto, contracts, PCA agent runtime
/services/            # proofgate/, ledger_service/, boundary_service/, context_forge/,
                      # mailops/ (MailLedger bridge), chatops/ (Command Router)
/modules/             # cfe/, lexqft/, qtmp/ (+ research: hde/, qoc/, ei/, lcsi/), ethics/ (equity-meter, HHE)
/plugins/             # packs-law/, packs-fin/, packs-code/, packs-sec/, packs-med/
/clients/             # web/ (CERT-Cockpit), desktop/ (Tauri), mobile/ (Flutter)
/schemas/             # pco.schema.json, policy.schema.json, data_pco(DPCO), model_pco(MCO)
/policies/            # pco/ policy_pack.yaml, governance_pack.yaml
/ci/                  # workflows (SLO Gate)
/infra/               # docker-compose, k8s, otel, grafana
/scripts/             # sbom/validate/sign/anchor
/docs/                # ADR, runbooki, manifesty
```

---

## 3) Rdzeń (Core) i Usługi (Services)

- **Truth Engine (TE):** reguły, SMT (Z3/CVC5), kontrakty publikacji.
- **ProofGate:** `POST /v1/proofgate/publish` → `{status ∈ PUBLISH|CONDITIONAL|PENDING|ABSTAIN, pco, ledger_ref}`.
- **PCO Ledger:** Merkle DAG; **podpis hybrydowy** _Ed25519 + ML-DSA (Dilithium)_; **FROST** 2-z-3; public payloads (bez PII); replikacja; **kotwice czasu** (OpenTimestamps).
- **Boundary (append-only, holografia):** `bulk_reconstruct()`; metryki: `boundary.delta_bits == 0`, `boundary.size_bytes`, `boundary.compression_ratio`, `boundary.shards`.
- **Context Forge:** cfpack (sesja+repo+symbol-map); `pack/unpack`; import/eksport **ContextKit** (Knowledge State vN).
- **MailOps (MailLedger bridge):** IMAP/SMTP/Webhook → _MIME normalizer_ → _Attachment Extractor_ → Evidence DAG; PCO/PNIP dla e-maili; forensics, multi-region.
- **ChatOps (Command Router):** jedno wejście tekstowe → mapowanie komend na API CFE/QTMP/devices/Domain Packs; hard Proof-Gate.
- **PCA — Proof-Carrying Agents:** każdy agent (usługa/worker) działa **wyłącznie** z ważnym PCO-tokenem zdolności; polityki OPA/Rego.

**Crypto & Supply-chain:** Ed25519+ML-DSA (hybryda), **FROST 2-z-3**; **SLSA 3+**, **in-toto**, **SBOM CycloneDX**, obrazy OCI z **cosign**, skan **trivy** (deny-by-default).
**Profile:** **Bunkier** (TEE: TDX/SEV-SNP/SGX) z attestation; **Chmura** (zero-trust bez TEE).

---

## 4) Proof-native I/O i **ProofFS**

- **PNIP/UPN** na wejściu (hash, podpis, jurysdykcja, polityka).
- **Proof-Only Sockets:** brak PCO na wyjściu ⇒ DROP.
- **ProofWASM (WASI Preview 2):** capability-security, brak sieci bez flag.
- **ProofFS (pfs\://):** montowalny FS (read-only) egzekwujący PNIP/PCO na plikach; eksport Merkle-dowodów; polityki dostępu w Boundary.
  - `pfs://mail/<messageId>` – załączniki e-maili jako read-only artefakty dowodowe.

---

## 5) **CFE** — pełna geometria sensu (API + metryki)

- **Krzywizny:** `GET /v1/cfe/curvature` → `{R, Ricci_max, kappa_max}`.
- **Geodezyjny Dowód:** `POST /v1/cfe/geodesic` → `{path, geodesic_action}`; **PCO:** `cfe.geodesic_action`.
- **Horyzont Zdarzeń Dowodowych:** `POST /v1/cfe/horizon` → `{locked, horizon_mass}`; **PCO:** `cfe.horizon_mass`.
- **Normatywne Soczewkowanie:** `GET /v1/cfe/lensing` → `{lensing_map, critical_precedents[]}`.
- **Dylatacja Czasu Prawnego:** **PCO:** `cfe.lapse_N`.

---

## 6) **lexqft** — ścieżki i zjawiska kwantowe

**Path-Coverage Gate (CI):** `coverage_gamma ≥ 0.9`, `uncaptured_mass ≤ 0.05`.
**Zjawiska (endpointy/PCO):**

- **Tunelowanie dowodowe:** `POST /v1/lexqft/tunnel {state_uri, barrier_model, evidence_energy}` → `{p_tunnel, min_energy_to_cross, path}`; **PCO:** `qlaw.tunneling.{prob, barrier_energy, path_length, model_uri}`.
- **Wirtualne pary argument–antyargument:** `POST /v1/qoc/vacuum_pairs {state_uri, budget_tokens}` → `{pairs, realization_threshold, realized}`; **PCO:** `qlaw.vacuum_pairs.{generated, realized, energy_debt}`, `realization_evidence_ids[]`.
- **Renormalizacja autorytetu precedensu:** `POST /v1/cldf/renormalize {citation_id, scale_mu}` → `{authority_mu, beta, fixed_points}`; **PCO:** `cldf.renorm.{scale, authority, beta, fixed_point}`.
- **SSB zgody:** `POST /v1/consent/ssb/init|freeze` → `{order_param_0 | state, freeze_time}`; **PCO:** `consent.{order_param, state, freeze_time}`.

---

## 7) **QTMP** — Teoria Pomiaru (stan $|Ψ⟩$, obserwable, nieoznaczoność)

**Funkcja falowa:**

$$
|\Psi_{\text{case}}\rangle = \sum_i c_i\,|\text{werdykt}_i\rangle,\quad \sum_i |c_i|^2=1
$$

Baza (konfigurowalna): `{"ALLOW","DENY","ABSTAIN",...}`.

**Operatory (Hermitowskie):** Ŵ (Werdykt), Î (Zamiar: _dolus_directus, dolus_eventualis, culpa_), Ĉ (Zgoda: _ważna/nieważna/warunkowa_), Ļ (Litera), Ŧ (Telos).
**Nieoznaczoność:** $\mathrm{Var}(L)\mathrm{Var}(T) \ge \tfrac{1}{2}|\langle[\hat L,\hat T]\rangle|$.
**Splątanie:** miary `qtm.entanglement.{mi,negativity}`.
**Dekoherecja/kolaps:** `qtm.decoherence.channel ∈ {dephasing, depolarizing, damping}` + `public_disclosure:email`.
**Kolejność pomiarów:** **obowiązkowe** `qtm.sequence[] (operator, timestamp, source)`; `source ∈ {ui, chatops:<cmd>, mail:<mail_id>}`.

**API (skrót):**
`POST /v1/qtm/init_case` → `{state_uri, basis}` · `POST /v1/qtm/measure` → `{verdict, p, collapse_log}` · `POST /v1/qtm/commutator {A,B}` → `{value}` · `POST /v1/qtm/find_entanglement`.

**Telemetria/KPI (PCO):**
`qtm.predistribution[]`, `qtm.collapse_event/prob/latency_ms`, `qtm.uncertainty_bound.L_T`, `qtm.entanglement.{mi,negativity}`, `qtm.decoherence.channel`, `qtm.sequence[]`.

---

## 8) Warstwa **devices/** (Maszyny Metawszechświata)

- **Horizon Drive Engine (HDE):** odwrotne CFE → plan dowodów do horyzontu.
  `POST /v1/devices/horizon_drive/plan` → `{evidence_plan, cost, expected_kappa}`; **PCO:** `plan_of_evidence[]`, `expected_kappa`, `budget_tokens`.
- **Quantum Oracle (QOC):** zapytania na superpozycji bez kolapsu.
  `POST /v1/devices/qoracle/expectation` → `{optimum, payoff, distribution}`.
- **Entanglement Inducer (EI):** syntetyzacja splątania.
  `POST /v1/devices/entangle` → `{target_negativity, certificate}`.
- **Chrono-Synclastic Infundibulum (LCSI/chronosync):** zgodzenie sprzecznych doktryn.
  `POST /v1/devices/chronosync/reconcile` → `{coords, pc_delta, treaty_clause_skeleton}`.
  **Governance:** publikacja wyników _wyłącznie_ z PCO; **AFV/ASE/ATC/ATS/AVR** = green.

---

## 9) Domain Packs (wtyczki, wspólny ABI)

**Kontrakt:** `init()`, `capabilities()`, `handle(task|query|email|chat_command)`, `export_pco()`.

### 9.1 Law (LEXENITH)

Micro-Court, CLDF/LEX-FONTARIUS (cytaty z hash), generatory pism, orzecznictwo, **PCΔ** i **Why-Not**; **DR-Replay/Recall**; profile jurysdykcji (PL→UE→świat) przez Ω-Kernel.

### 9.2 Finance — **FINENITH / „Quantum Alpha”**

**Operatory:** $\hat R$ (Ryzyko), $\hat S$ (Sentyment), **nieoznaczoność** $[\hat R,\hat S]\neq 0$.
**Splątanie aktywów:** telemetria `fin.entanglement.mi`.
**Endpointy:**
`POST /v1/fin/alpha/measure` → `{outcome, p, pco}`
`GET  /v1/fin/alpha/uncertainty` → `{lower_bound}`
`GET  /v1/fin/alpha/entanglements` → `{pairs, mi}`
**Polityki:** limity ryzyka, ślady danych, DP/ZK dla wrażliwych sygnałów; SLO per-asset.

### 9.3 Code/Sec/Med

- **Code:** operator „Test” (komutuje/niekomutuje z „Coverage”), kolaps hipotez przy refaktorach, DPCO dla źródeł.
- **Sec:** operator „Exploitability” vs „BlastRadius”, pentest jako QTMP, ProofFS dla artefaktów.
- **Med:** zgoda (Ĉ) z SSB; normy HIPAA/RODO jako transformy Ω-Kernel; DPCO dla danych klinicznych.

---

## 10) **UPN Registry** & Revocation

- `POST /v1/upn/register` · `POST /v1/upn/revoke` (public payload + Merkle-dowód unieważnienia).
- **DR-Replay/Recall** spina się z UPN Registry (linki w Ledgerze); TTL/retencja, polityki kasowania z dowodem.

---

## 11) **PCO** — schema (wymagane i rozszerzenia)

**Wymagane:** `spec`, `claims[]`, `subject`, `proof{type,root,signatures[],threshold}`.
**Rozszerzenia (opcjonalne, wersjonowane):**

- `metrics.*`, `verdicts.*`, `compute.{cost_tokens,budget_tokens}`, `governance.*`,
- `why_not.trace_uri`, `pc_delta.uri`, `refutations[]`,
- `cfe.{geodesic_action,horizon_mass,lapse_N}`,
- `qtm.{basis,predistribution,sequence[],uncertainty_bound.*,entanglement.*,decoherence.*,collapse_*}`,
- `qlaw.tunneling.*`, `cldf.renorm.*`, `consent.*`,
- `fin.entanglement.*`,
- **DPCO (Data-PCO):** `dataset.hash, lineage[], dp_epsilon, consent_refs[]`,
- **MCO (Model-PCO):** `training.data_dpco[], sbom_uri, commit_sha, eval.{ece,brier,auroc}, bias_report_uri`,
- **MailOps:** `io.email.{mail_id,thread_id,spf,dkim,dmarc}`,
- **ChatOps:** `chatops.cmd`, `chatops.args`, `chatops.openapi_rev`.

---

## 12) **Equity-Meter & HHE (Double-Verdict)**

- **Equity-Meter:** metryki sprawiedliwości (np. 1-Wasserstein między rozkładami decyzji), `equity.score ∈ [0,1]`.
- **HHE:** gdy `equity.score < floor` lub konflikt aksjologiczny — generuj **Double-Verdict** (Ŵ_litera, Ŧ_telos) + Why-Not/PCΔ, eskalacja do **ATS/AVR**.
- **API:** `POST /v1/ethics/equity_meter` → `{score, deltas}` · `POST /v1/ethics/double_verdict` → `{verdicts, rationale}`.

---

## 13) **CI/SLO-Gate — progi twarde**

- **Testy/Lint/Typy/Security/Secrets** — zielone (pytest/coverage; ruff/black/mypy/yamllint; bandit/secret-scan).
- **Policy/PCO Gate** — zgodność schematów i statusów.
- **Gauge-Gate:** `gauge.holonomy_drift ≤ ε` (np. 1e-3).
- **Path-Coverage Gate (lexqft):** `coverage_gamma ≥ 0.9`, `uncaptured_mass ≤ 0.05`.
- **Boundary-Rebuild:** `boundary.delta_bits == 0`; raport `bits_delta_map` per shard.
- **Supply-chain:** SBOM + in-toto + cosign wymagane (deny-by-default).
- **SLO:** p95 latencja API, error-budget, alerty **multi-burn-rate** (SEV-1/2/3).

---

## 14) Bezpieczeństwo i Prywatność

- **PQ-crypto:** Ed25519 + ML-DSA (hybrydowo), **FROST 2-z-3**.
- **Confidential Computing:** TEE (profil Bunkier), remote attestation w ProofGate.
- **Prywatność:** ZK-dowody atrybutów; **MPC**; **Differential Privacy** (budżet `ε` w PCO); _data minimization by design_.
- **Sieć/tożsamość workloadów:** mTLS **SPIFFE/SPIRE**, autz **OPA/Rego**, **QUIC+MASQUE**, rate-limit (token bucket) + **load-shedding sterowany QTMP**.

---

## 15) Observability & Data-plane

- **OTel** tracing + **eBPF** (profiling/flow) + continuous profiling (Pyroscope/Parca).
- Evidence: S3/MinIO (**WORM** dla cold), indeksy **Arrow/Parquet**, strumienie **Kafka/Redpanda**, **CRDT** dla nie-krytycznych replik.
- SRE: SLO per-tenant, **cardinality budgets**, GameDays, shadow traffic, canary/progressive delivery, regularne **DR-drills**; snapshoty boundary off-site.

---

## 16) Klienci (UX) — **CERT-Cockpit**

Zakładki: **Geometry | Quantum | Boundary** + **ChatOps (Command Palette)**.

- **Geometry:** Ricci, lensing, horyzont (lock).
- **Quantum:** Operator Composer (W/I/C/L/T), log `qtm.sequence`, heatmap komutatorów, graf splątań.
- **Boundary:** shards, compression, reconstruct, anchoring.
- **ChatOps:** jedno okno tekstowe; autouzupełnianie z OpenAPI; historia komend to część **Knowledge State** (Context Forge).
- **Przyciski:** **Why-Not/PCΔ**, **DR-Replay**, **Allocate budget** (dla `PENDING`).
- **Marketplace** wtyczek: Law/Finance/Code/Sec/Med; rozliczanie subskrypcji.

---

## 17) CLI (cerctl) — skróty

```
cerctl init                         # szkielet repo + CI + policies
cerctl pco sign in.json             # podpis PCO (hybryda; FROST)
cerctl pack thread.json             # cfpack z wątku/artefaktów
cerctl ledger get CER-1             # public payload sprawy
cerctl boundary reconstruct --date 2025-08-30
```

---

## 18) Dev Setup — komendy

```
uv venv && source .venv/bin/activate && uv pip install -r requirements.txt
docker compose -f infra/docker-compose.dev.yml up -d --build
pytest -q && ruff check . && black --check . && mypy . && yamllint .
uvicorn services.proofgate.app:app --reload --port 8081
uvicorn services.boundary_service.app:app --reload --port 8082
```

---

## 19) Przepływ informacji (run-time)

1. **Ingest** (MailOps/Repo/Upload) → Evidence DAG + Casefile meta.
2. **Analiza** (TE/lexqft/CFE/QTMP) → kandydaci wyników + kontrdowody.
3. **Decyzja ProofGate** → status + PCO + podpis + wpis do Ledger.
4. **Publikacja** (public payload) → weryfikowalny link/merkle proof.
5. **Continuity** (cfpack) → dalsza praca bez utraty kontekstu.

---

## 20) API — katalog (skrót kompletny)

**ProofGate:** `POST /v1/proofgate/publish`
**Ledger:** `GET /v1/ledger/{case_id}`
**Boundary:** `POST /v1/boundary/reconstruct {date}` → `{ok, delta_bits, bits_delta_map}`
**Continuity:** `POST /v1/continuity/pack` · `POST /v1/continuity/unpack` · `POST /v1/continuity/import_contextkit` · `GET /v1/continuity/export_contextkit?v=latest`
**MailOps:** `POST /v1/mail/ingest` · `GET /v1/mail/{mail_id}` · `POST /v1/mail/reply` _(wymaga PCO)_
**ChatOps:** `POST /v1/chatops/command` · `GET /v1/chatops/skills` _(Proof-Gate dla komend publikujących)_
**CFE:** `GET /v1/cfe/curvature` · `POST /v1/cfe/geodesic` · `POST /v1/cfe/horizon` · `GET /v1/cfe/lensing`
**QTMP:** `POST /v1/qtm/init_case` · `POST /v1/qtm/measure` · `POST /v1/qtm/commutator` · `POST /v1/qtm/find_entanglement`
**lexqft/Q-law:** `POST /v1/lexqft/tunnel` · `POST /v1/qoc/vacuum_pairs` · `POST /v1/cldf/renormalize` · `POST /v1/consent/ssb/*`
**Devices:** `POST /v1/devices/horizon_drive/plan` · `POST /v1/devices/qoracle/expectation` · `POST /v1/devices/entangle` · `POST /v1/devices/chronosync/reconcile`
**Law exports:** `GET /v1/case/{case_id}/why_not` · `GET /v1/case/{case_id}/pc_delta`
**DR:** `POST /v1/dr/replay` · `POST /v1/dr/revoke`
**Costs:** `GET /v1/cost/budget` · `POST /v1/cost/allocate`
**Finance (FINENITH):** `POST /v1/fin/alpha/measure` · `GET /v1/fin/alpha/uncertainty` · `GET /v1/fin/alpha/entanglements`
**UPN:** `POST /v1/upn/register` · `POST /v1/upn/revoke`

---

perfekcyjnie — poniżej masz gotowy, **rozszerzony rozdział do Manifestu** (wklej jako sekcję 21). Zostawiłem PL/EN, twarde zasady i **konkretne przykłady** w Python/TS+React/Go/Rust/Bash/HTML/YAML/JSON Schema/SQL, plus konwencje commitów i testy. Kopiuj-wklej bez zmian.

---

## 21) Standard Kodowania — **Premium Code Style** <a name="standard"></a>

**Cel:** kod ma być czytelny, przewidywalny, testowalny, _proof-native_ (PCO/PNIP), z domyślną telemetrią i bezpieczeństwem.

### 21.1 Nagłówek pliku (ForgeHeader v1)

**Zawsze na górze pliku**:

- **Baner ASCII** z nazwą i rolą (PL/EN).
- **Docstring modułu** (PL/EN, 1–2 zdania).
- Sekcje w kodzie z nagłówkami:
  `# === KONFIGURACJA / CONFIGURATION ===`, `# === MODELE / MODELS ===`, `# === LOGIKA / LOGIC ===`, `# === I/O / ENDPOINTS ===`, `# === TESTY / TESTS ===`.

**Przykład (Python):**

```python
# +-------------------------------------------------------------+
# |                CERTEUS - Ingest Service (API)               |
# +-------------------------------------------------------------+
# | PLIK / FILE: services/ingest_service/models.py              |
# | ROLA / ROLE:                                                |
# |  PL: Modele ingestu (fakty, źródła, metryki).               |
# |  EN: Ingest data models (facts, sources, metrics).          |
# +-------------------------------------------------------------+

"""PL: Modele danych dla ingest. EN: Data models for ingest."""
from __future__ import annotations

# === IMPORTY / IMPORTS ===
from pydantic import BaseModel, Field
from typing import List, Optional
from datetime import datetime

# === MODELE / MODELS ===
class EvidenceItem(BaseModel):
    upn: str = Field(..., description="Unique Proof Number")
    sha256: str
    source_uri: str
    received_at: datetime

class IngestRequest(BaseModel):
    items: List[EvidenceItem]
    pnip_client: str

# === LOGIKA / LOGIC ===
def validate_items(req: IngestRequest) -> None:
    """PL: Walidacja wejścia. EN: Input validation."""
    if not req.items:
        raise ValueError("empty_ingest")
```

**Przykład (Shell):**

```bash
#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                    CERTEUS - DRAT Checker                   |
# +-------------------------------------------------------------+
# | FILE: scripts/check_drat.sh                                 |
# | ROLE: Verify DRAT files (stub/real).                        |
# +-------------------------------------------------------------+
set -Eeuo pipefail
trap 'echo "[ERR] line:$LINENO status:$?" >&2' ERR
```

**Przykład (HTML):**

```html
<!--
+-------------------------------------------------------------+
|            CERTEUS - Proof Visualizer (Skeleton)            |
+-------------------------------------------------------------+
| FILE: clients/web/proof_visualizer/index.html               |
| ROLE: Placeholder UI for interactive proof graph.           |
+-------------------------------------------------------------+
-->
<!DOCTYPE html>
<html lang="pl" data-theme="light">
  ...
</html>
```

---

### 21.2 Nazewnictwo i struktura

- **Pliki/zmienne/funkcje:** `snake_case` • **Klasy/Typy:** `PascalCase` • **Stałe:** `UPPER_CASE`.
- **Katalogi domenowe:** `packs-<domain>/<pack_name>/...` (np. `packs-law/lexenith/...`).
- **Testy:** `tests/test_<module>.py` (pytest), `*_spec.ts` (vitest/jest), `*_test.go` (Go).
- **Artefakty build:** do `dist/` lub `build/`; **żadnych** artefaktów w git.
- **Public API** musi mieć docstring PL/EN i typy (gdzie to możliwe – _strict mode_).

---

### 21.3 Błędy, logowanie, telemetria

- **Błędy API**: envelope `{code, message, correlation_id, pco?}`; nigdy nie logujemy sekretów.
- **OTel**: każdy request ma `trace_id/span_id`; logi strukturalne `jsonl`.
- **Telemetry prefixy:** `cfe.*`, `qtm.*`, `boundary.*`, `ledger.*`, `io.email.*`, `chatops.*`.

**Przykład (Go – handler):**

```go
// +-------------------------------------------------------------+
// | CERTEUS - ProofGate (HTTP Handler)                          |
// +-------------------------------------------------------------+
package proofgate

import (
  "encoding/json"
  "net/http"
)

type ErrorEnvelope struct {
  Code          string `json:"code"`
  Message       string `json:"message"`
  CorrelationID string `json:"correlation_id"`
  PCO           any    `json:"pco,omitempty"`
}

func writeErr(w http.ResponseWriter, status int, code, msg, corr string) {
  w.Header().Set("Content-Type", "application/json")
  w.WriteHeader(status)
  _ = json.NewEncoder(w).Encode(ErrorEnvelope{
    Code: code, Message: msg, CorrelationID: corr,
  })
}
```

---

### 21.4 **Proof-Native**: PNIP/PCO w kodzie

- Wejście musi mieć **PNIP** (hash, podpis, jurysdykcję, politykę).
- Wyjście publikowalne ma **PCO** (schema + podpis + odnośnik do ledger).
- Brak PCO na wyjściu → **DROP** (Proof-Only Sockets).

**Przykład (Python – opakowanie PCO):**

```python
# === PCO / PROOF WRAP ===
from hashlib import sha256
from typing import Dict, Any

def make_pco(payload: Dict[str, Any], sign) -> Dict[str, Any]:
    """
    PL: Buduje kapsułę PCO i podpisuje.
    EN: Builds and signs a Proof-Carrying Output capsule.
    """
    root = sha256(repr(sorted(payload.items())).encode()).hexdigest()
    sig  = sign(root)  # HSM/KMS/FROST
    return {"spec":"pco.v0.2","subject":payload.get("subject",""),
            "claims":[payload], "proof":{"type":"hybrid","root":root,
            "signatures":[sig], "threshold":1}}
```

---

### 21.5 Przykłady językowe (end-to-end)

#### 21.5.1 Python (FastAPI endpoint z PCO + OTel)

```python
# === I/O / ENDPOINTS ===
from fastapi import APIRouter, Depends, HTTPException, Request
from opentelemetry import trace
router = APIRouter()

@router.post("/v1/cfe/geodesic")
async def geodesic(req: IngestRequest, request: Request):
    """PL: Geodezyjny dowód. EN: Geodesic proof."""
    span = trace.get_tracer(__name__).start_span("cfe.geodesic")
    try:
        validate_items(req)
        result = {"path":[...], "geodesic_action": 12.34, "subject": req.pnip_client}
        pco = make_pco(result, sign=lambda r: {"alg":"Ed25519","sig":"..."} )
        return {"ok":True, "pco":pco}
    except ValueError as e:
        raise HTTPException(status_code=400, detail={"code":str(e),"pco":None})
    finally:
        span.end()
```

#### 21.5.2 TypeScript + React (UI panel z PCO i walidacją)

```tsx
/* +-------------------------------------------------------------+
 * | CERTEUS - Measurement Panel (ChatOps aware)                 |
 * +-------------------------------------------------------------+ */
import React, { useState } from "react";

type MeasureResp = { verdict: string; p: number; pco?: unknown };

export function MeasurementPanel(): JSX.Element {
  const [verdict, setVerdict] = useState<string>("-");
  async function onMeasure() {
    const res = await fetch("/v1/qtm/measure", { method: "POST", body: "{}" });
    const data: MeasureResp = await res.json();
    if (!data.pco) throw new Error("no_pco_response");
    setVerdict(`${data.verdict} (p=${data.p.toFixed(3)})`);
  }
  return (
    <div className="p-4 border rounded-2xl">
      <h3 className="font-semibold">QTMP: Measurement</h3>
      <button className="btn" onClick={onMeasure}>
        Measure
      </button>
      <div className="mt-2">
        Verdict: <strong>{verdict}</strong>
      </div>
    </div>
  );
}
```

#### 21.5.3 Rust (ProofFS: tylko read-only)

```rust
// +-------------------------------------------------------------+
// | CERTEUS - ProofFS Mount (RO)                                |
// +-------------------------------------------------------------+
use anyhow::Result;
fn mount_read_only(uri: &str) -> Result<()> {
    // PL: Montuje pfs:// jako tylko-do-odczytu.
    // EN: Mounts pfs:// read-only.
    if !uri.starts_with("pfs://") { anyhow::bail!("invalid_uri"); }
    // ... implementacja sterownika ...
    Ok(())
}
```

#### 21.5.4 Bash (strict mode + PNIP check)

```bash
#!/usr/bin/env bash
set -Eeuo pipefail
: "${PNIP_CLIENT:?PNIP_CLIENT required}"

if [[ -z "${INPUT_JSON:-}" ]]; then
  echo '{"code":"missing_input","message":"INPUT_JSON empty"}' >&2; exit 64
fi
jq -e '.pnip_client and .items' <<<"$INPUT_JSON" >/dev/null \
  || { echo '{"code":"pnip_invalid"}'; exit 65; }
```

#### 21.5.5 YAML (GitHub Actions – Gates)

```yaml
# +-------------------------------------------------------------+
# | CERTEUS - CI Gates (Gauge/PathCoverage/Boundary)           |
# +-------------------------------------------------------------+
name: ci-gates
on: [push, pull_request]
jobs:
  gates:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: uv pip install -r requirements.txt
      - name: Gauge-Gate
        run: python scripts/gates/gauge_gate.py --epsilon 1e-3
      - name: Path-Coverage Gate
        run: python scripts/gates/path_coverage_gate.py --min 0.90
      - name: Boundary-Rebuild
        run: python scripts/gates/boundary_rebuild.py --must-zero
```

#### 21.5.6 JSON Schema (PCO – rozszerzenie MailOps/ChatOps)

```json
{
  "$id": "schemas/pco.extensions.mailops.chatops.json",
  "type": "object",
  "properties": {
    "io.email": {
      "type": "object",
      "properties": {
        "mail_id": { "type": "string" },
        "thread_id": { "type": "string" },
        "spf": { "type": "string" },
        "dkim": { "type": "string" },
        "dmarc": { "type": "string" }
      },
      "required": ["mail_id"]
    },
    "chatops": {
      "type": "object",
      "properties": {
        "cmd": { "type": "string" },
        "args": { "type": "array", "items": { "type": "string" } },
        "openapi_rev": { "type": "string" }
      },
      "required": ["cmd"]
    }
  }
}
```

#### 21.5.7 SQL (migracja odwracalna)

```sql
-- +-------------------------------------------------------------+
-- | CERTEUS - Migration: add_pco_index                         |
-- +-------------------------------------------------------------+
-- PL: Dodaje indeks po root (PCO). EN: Adds index by PCO root.
BEGIN;
  CREATE INDEX CONCURRENTLY IF NOT EXISTS idx_pco_root ON ledger (pco_root);
COMMIT;
-- DOWN:
-- BEGIN; DROP INDEX IF EXISTS idx_pco_root; COMMIT;
```

---

### 21.6 Testy (TDD, property-based, snapshot PCO)

**Python (pytest + hypothesis):**

```python
# tests/test_pco_wrap.py
from hypothesis import given, strategies as st
from services.ingest_service.models import IngestRequest, EvidenceItem
from pco.wrap import make_pco

@given(st.text(min_size=1))
def test_make_pco_root_is_hex(subject):
    req = {"subject": subject, "value": 1}
    pco = make_pco(req, sign=lambda r: {"alg":"Ed25519","sig":"X"})
    assert "proof" in pco and len(pco["proof"]["root"]) == 64  # sha256 hex
```

**Snapshot (struktura PCO):**

```python
def test_pco_contract(snapshot):
    payload = {"subject":"CER-1","value":42}
    pco = make_pco(payload, sign=lambda r: {"alg":"Ed25519","sig":"X"})
    snapshot.assert_match({k: bool(v) if k=="proof" else v for k,v in pco.items()}, "pco_contract.json")
```

---

### 21.7 Bezpieczeństwo (minimum operacyjne)

- **Sekrety** tylko przez KMS/HSM; brak `print(secret)`.
- **Deserializacja**: używamy bezpiecznych bibliotek (pydantic, serde).
- **HTTP**: `application/json`, _no_ wildcard CORS w produkcji.
- **Sandbox**: pluginy w **ProofWASM** (WASI, capability-security).
- **Dane wrażliwe**: DP/MPC/ZK – polityki w Boundary; logowanie z maskowaniem.

---

### 21.8 Commity, PR, TODO

- **Conventional Commits**:
  `feat(cfe): geodesic endpoint + PCO`, `fix(qtmp): guard for empty basis`, `chore(ci): add gates`.
- **Body PR**: _Goal / Change / Paths / API / Tests / Accept_ + link do PCO artefaktów.
- **TODO**: `# TODO(T123): ...` (task id), z datą i kryterium akceptacji.

---

### 21.9 Linty i formatery

- **Python**: `ruff`, `black`, `mypy`, `pytest`, `coverage`.
- **TS/React**: `eslint --max-warnings=0`, `tsc --noEmit`, `vitest`.
- **Go**: `go vet`, `staticcheck`, `golangci-lint`, `go test ./...`.
- **Rust**: `cargo clippy -- -D warnings`, `cargo fmt --check`, `cargo test`.

---

### 21.10 Mini-checklista pliku

- [ ] ForgeHeader v1 (baner + docstring PL/EN).
- [ ] Sekcje kodu z nagłówkami.
- [ ] Typy/Docstrings dla publicznych symboli.
- [ ] Telemetria (OTel), brak sekretów w logach.
- [ ] Wejście PNIP, wyjście PCO (jeśli publikowalne).
- [ ] Test(y) + kryteria CI (gates).

---

**Koniec sekcji 21.**

---

## 22) Governance, Billing i Public Modules

- **ZHG Governance Pack:** role: **AFV/ASE/ATC/ATS/AVR** – _wymagane_ zielone przed publish/merge.
- **Billing & Proof-Cost Tokens:** brak środków ⇒ `PENDING` + plan.
- **Public Modules (opcjonalne):** Citizen zk-Query, Treaty OS, Energy/CO₂ Ledger (flagi build; domyślnie OFF).

---

## 23) SYNAPSY (P2P) — plan

Transport **QUIC/Noise**, multipath; **DHT** kompetencji; fraktalny router (lokalnie → regionalnie → globalnie). Start: „Bus↔P2P bridge”, potem wygaszanie bus; deterministyczne kolejki i podpisy tras.

---

## 24) Roadmap (operacyjna)

1. Włączyć progi CI (**Gauge/Path-Coverage/Boundary**) + supply-chain deny-by-default.
2. Ujawnić CFE API (`geodesic/horizon/lensing`) + domknąć QTMP pola (`sequence[]`, `uncertainty_bound.*`).
3. Utworzyć **devices/** (HDE, Q-Oracle, Entangler).
4. Wypuścić **FINENITH „Quantum Alpha”** (R/S operators, entanglement, polityki).
5. Spiąć **UPN Registry** z DR-Replay/Recall; uruchomić PCA i ProofFS w produkcji.
6. Dodać DPCO/MCO do pipeline’u danych i modeli (data/model lineage „z dowodem”).
7. Uruchomić **MailOps & ChatOps** w trybie „strict Proof-Gate” jako domyślny interfejs użytkownika.

---

## 25) Threat Model & Security Invariants

**Inwarianty (nie negocjujemy):**

- **Proof-Only I/O** — brak PCO ⇒ **DROP**.
- **Boundary = append-only**, audyt odtwarzalny (`boundary.delta_bits == 0`).
- **PQ-crypto hybrydowo** (Ed25519 + ML-DSA), **FROST 2-z-3**, rotacja kluczy wg harmonogramu (§26).
- **Brak PII w Ledger (public payload)**; PII wyłącznie w warstwie danych z polityką dostępu (OPA/Rego) i DPCO.
- **Sandbox**: pluginy w **ProofWASM (WASI)**; „escape” tylko przez whitelisting z PCO.
- **Reproducible builds** + **SLSA/in-toto/SBOM**; deny-by-default.

**Model zagrożeń (STRIDE → Kontrole):**

- **S**poofing → mTLS (SPIFFE/SPIRE), PCO-tokeny zdolności (PCA).
- **T**ampering → Merkle-DAG, WORM, podpisy hybrydowe, attestation (TEE).
- **R**epudiation → PCO/UPN, kotwice czasu, nieusuwalne logi audytowe.
- **I**nformation disclosure → DP/MPC/ZK; redakcja/maskowanie; ProofFS (RO).
- **D**oS → rate-limit + **load-shedding sterowany QTMP**; „brownout modes”.
- **E**levation → OPA/Rego + least privilege; feature-gates; supply-chain policy.

---

## 26) Data Governance & Retention (DPCO/MCO)

**Klasy danych:** Public / Restricted / Sensitive (domyślnie _Restricted_).

**DPCO (Data-PCO):** `dataset.hash, lineage[], dp_epsilon, consent_refs[]` (powiązane z Boundary/Consent SSB).

**Retencja i kasowanie:**

- Evidence RAW (Sensitive): **T**=180 dni (WORM), potem redakcja i hash-only (lineage).
- Artefakty modelowe (MCO): T=12 mies., z pełnym **SBOM** i commit-pin.
- **UPN revoke**: kasowanie z dowodem (Merkle-proof) + `DR-Recall` link.

**Rotacja kluczy:** KDS policy `rotate:<ed25519:90d|ml-dsa:180d|frost-shares:90d>`; roll-forward, nie roll-back.

---

## 27) Release / Branching / Promotion

**Strategia:** trunk-based (preferowane) lub krótki GitFlow.

**Zasady ochrony gałęzi:**

- PR z zielonymi **gates** (§13) + **ZHG** (AFV/ASE/ATC/ATS/AVR = green).
- Tagowanie **SemVer**; changelog generowany automatem (Conventional Commits).

**Promocja środowisk:** `dev → stage → prod`

- „Freeze window” + canary/progressive delivery.
- Dowód promocji: PCO z zestawem attestations (build, test, gates, sign).

---

## 28) Versioning & Compatibility (API/ABI Packs)

**API:** `/v{major}/...`; 1-major overlap na deprecacje (warn w ChatOps/ProofGate).

**ABI dla Domain Packs:**

- `pack_abi.major.minor` + `capabilities()`; **Compatibility Matrix** (Core↔Pack).
- Feature-gates: `features: ["qtmp.sequence","fin.splitting.mi"]`.

**Breaking rules:** Zmiany pól obowiązkowych w PCO/PNIP/MCO/DPCO ⇒ **major bump**.

---

## 29) Performance & Capacity (Budżety)

**Budżety:**

- p95 **API** ≤ 250 ms (intra-DC), p99 błędów ≤ 0.5%/30d.
- **CFE/lexqft/QTMP**: budżet `compute.cost_tokens` na request z **hard cap** (ProofGate).
- **Kolejki**: max **queue_time** 200 ms; load shedding przez `qtm.lapse_N` i priorytety.

**Sizing (guideline):**

- Front (ProofGate/ChatOps): CPU-heavy, 1 vCPU/600 RPS (p95 200 ms).
- CFE/QTMP: GPU opcjonalnie; batch window ≤ 50 ms; pre-allocation pamięci.

---

## 30) OpenAPI & SDK

**Spec:** `docs/openapi/certeus.v1.yaml` (generowany w CI).

**SDK (SemVer):**

- Python: `pip install certeus-sdk` — `CerteusClient(base_url).cfe.geodesic(...)`.
- TS/Node: `npm i @certeus/sdk` — `client.qtm.measure({})`.
- Go: `go get github.com/ORG/REPO/sdk/go`.

**Kontrakt:**

- SDK ma wbudowane walidatory PNIP/PCO.
- Wersja SDK ≤ wersji API (kompatybilność w dół w obrębie major).

---

## 31) Compliance Map (ISO/SOC2/RODO)

**ISO 27001:** A.5 (polityki), A.8 (asset mgmt), A.12 (operacje), A.14 (system devel), A.18 (zgodność) → mapowanie do modułów (Boundary/ProofGate/OPA/DP).

**SOC2:** Security/Availability/Confidentiality → gates + SLO + DR-drills.

**RODO:** Minimalizacja danych, prawo do bycia zapomnianym (UPN/DR-Recall), DPIA dla Domain Packs Med/Sec/Fin.
_(To nie porada prawna. Sekcja wskazuje implementacyjne punkty zaczepienia.)_

---

## 32) End-to-End Cookbooks (2 przepływy)

**32.1 MailOps → Decyzja (Law):**

1. `POST /v1/mail/ingest` (MIME b64) → Evidence DAG + `pfs://mail/<id>`.
2. `POST /v1/cfe/geodesic` (case) + `POST /v1/cfe/horizon` (lock).
3. `POST /v1/qtm/measure` (kolejność pomiarów `qtm.sequence[]: ["Ļ","Ŧ"]`).
4. `POST /v1/proofgate/publish` → **PCO** + wpis do **Ledger**.
5. `GET /v1/ledger/{case}` → public payload (bez PII) + Merkle-proof.

**32.2 ChatOps → HDE (plan dowodów):**

1. `POST /v1/chatops/command` `{cmd:"hde.plan --case CER-7 --budget 100"}`.
2. Router → `devices/horizon_drive/plan` (PCO z `plan_of_evidence[]`).
3. Operator zatwierdza budżet (`POST /v1/cost/allocate`).
4. Publikacja planu z PCO i linkiem do Boundary snapshot.

---

## 33) Testing Strategy & Quality Gates

**Piramida:** unit → integration → e2e → property-based → fuzz.

- **Unit:** ≥80% coverage na Core/Services.
- **Property-based:** QTMP/CFE (inwarianty: normalizacja, idempotencja transformacji).
- **E2E:** MailOps/ChatOps happy-path + błędy (Proof-Only).
- **Fuzz:** parsowanie PNIP/PCO/ProofFS; malformed MIME; API schema fuzz.
- **Drift tests:** `gauge.holonomy_drift ≤ ε`; `coverage_gamma ≥ 0.90`.

---

## 34) Incident Response & DR

**Severities:** P1 (ProofGate/Boundary down), P2 (SLO breach), P3 (degradacja częściowa).

**Proces:**

- On-call rota; war-room (ChatOps); decision log (PCO).
- **DR-Replay/Recall**: odtworzenie stanu na t=czas; RTO 30 min / RPO 5 min.
- **Postmortem (bez winnych)**: PCO z korektą polityk/gates.

---

## 35) UX: Accessibility & Localization

- **A11y:** WCAG 2.2 AA; kontrast ≥ 4.5:1; pełna nawigacja klawiaturą; ARIA-roles.
- **i18n:** PL/EN w UI/Docstring; **Ω-Kernel** wspiera `lang` jako transformację bazową.
- **Datetime/Zone:** wszystkie czasy ISO-8601 + TZ; klient wybiera prezentację.

---

## 36) Dokumentacja & ADR

- **ADR** (`docs/adr/ADR-xxxx-title.md`): decyzja, kontekst, konsekwencje, alternatywy.
- **Runbooki** (§15) + **Reference Guides** (`docs/guides/`) — CFE/QTMP/Devices.
- **Diagramy**: katalog `docs/diagrams/` (puml/mermaid); generowane w CI.

---

**Koniec Manifestu Jednolitego v1.5 (Immutable).**




