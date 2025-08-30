# Diagrams — CERTEUS

## Boundary Snapshot / Diff

```mermaid
flowchart TD
  A[data/public_pco/*.json] -->|hash| B[Shard assign (first 2 hex)]
  B --> C[Shard digest (SHA-256 of leaf digests)]
  C --> D[Global digest (concat shard-id + digest)]
  D --> E[out/boundary_snapshot.json]

  E1[BASE snapshot]:::snap --> F[boundary_diff]
  E2[HEAD snapshot]:::snap --> F
  F --> G{Identical?}
  G -- yes --> H[status: IDENTICAL]
  G -- no  --> I[status: DIFFERENT + shard diffs]

  classDef snap fill:#dde,stroke:#88a
```

## Proof Gate (CI) Pipeline

```mermaid
flowchart LR
  subgraph CI
    Lint[ruff] --> Pytest[pytest + JUnit]
    Pytest --> Gauge[scripts/gates/compute_gauge_drift.py]
    Pytest --> Coverage[scripts/gates/compute_lexqft_coverage.py]
    VerifyBundles[scripts/gates/compute_boundary_report.py] --> BoundaryGate
    Gauge --> GaugeGate[scripts/gates/gauge_gate.py]
    Coverage --> CoverageGate[scripts/gates/path_coverage_gate.py]
    BoundaryGate[scripts/gates/boundary_rebuild_gate.py]
    SLOMeasure[scripts/slo_gate/measure_api.py] --> SLOGate[scripts/slo_gate/check_slo.py]
    SBOM[cyclonedx-py] --> CosignSign[cosign sign-blob]
    Prov[scripts/supply_chain/make_provenance.py] --> CosignSign
    CosignSign --> CosignVerify[scripts/supply_chain/verify_cosign_artifacts.py]
    TruthGates[scripts/compute_truth_gates.py]
  end
```

## Packs (Discovery)

```mermaid
flowchart LR
  P[plugins/*] --> Loader[packs_core.loader.discover]
  Loader --> API[/GET /v1/packs/]
  API --> UI[ChatOps / Cockpit]
```

## ProofFS & MailOps → Boundary

```mermaid
flowchart LR
  subgraph Ingest
    M[MailOps /ingest] --> N[Normalize MIME + Attachments]
    N --> DPCO[io.email.* + attachments]
  end
  subgraph ProofFS (RO)
    DPCO --> P[pfs://mail/<messageId>]
  end
  P --> E[Evidence DAG]
  E --> B[Boundary append-only]
  B --> R[Reconstruct / Verify]
```
