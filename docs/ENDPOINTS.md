# CERTEUS — Endpoints (MVP)

- POST `/v1/pco/bundle`: Build + validate ProofBundle v0.2; optional SMT2 verification; writes public payload.
- GET `/pco/public/{case_id}`: Public PCO (zero PII); validates Merkle path and Ed25519 signature.
- GET `/.well-known/jwks.json`: JWKS with Ed25519 public key.
- GET `/metrics`: Prometheus metrics (SLOs and counters).
- POST `/v1/sources/cache`: Cache a legal source (digest + path + retrieved_at).
- POST `/v1/proofgate/publish`: Policy-based decision (PUBLISH/CONDITIONAL/PENDING/ABSTAIN).

## Marketplace & Packs (T13)

- Gate: Marketplace Policy (report‑only)
  - `python scripts/gates/marketplace_policy_gate.py`
  - Validates semver in `plugins/*/plugin.yaml`, license allowlist, signature metadata (if present).
- Gate: Pack ABI/SemVer (report‑only)
  - `python scripts/gates/pack_abi_semver_gate.py`
  - Compares ABI descriptor to `abi_baseline.json`; on ABI change requires MAJOR bump (when enforcement enabled).
- Baseline updater
  - `python scripts/packs/update_abi_baselines.py`
  - Creates/updates `plugins/<pack>/abi_baseline.json` from current module shape.

### API

- GET `/v1/packs/`: list packs `{name, version, abi, capabilities[], enabled, signature?}`
- POST `/v1/packs/enable`: body `{pack, enabled}` → toggles overlay state
- POST `/v1/packs/install`: body `{pack, signature, version?}` → persists signature and optional installed_version

See also `docs/openapi/certeus.v1.yaml` for full schemas and examples.

<<<<<<< HEAD
- GET `/v1/lexqft/coverage`: Aggregated path coverage gamma (`coverage_gamma`).
- GET `/v1/lexqft/coverage/state`: Coverage state with weighted `coverage_gamma` and `uncaptured_mass`.
- POST `/v1/lexqft/coverage/update`: Replace coverage contributions: `{gamma, weight, uncaptured}[]`.
- POST `/v1/lexqft/coverage/reset`: Reset coverage aggregator (clears persisted state).
- POST `/v1/lexqft/tunnel`: Tunneling heuristic; returns `{p_tunnel, min_energy_to_cross, path}` and emits PCO headers `X-CERTEUS-PCO-qlaw.tunneling.*`.
  - GET `/v1/lexqft/tunnel/scenarios`: returns example barrier models `{model_id, energy, model_uri}` for quick trials.

- POST `/v1/qoc/vacuum_pairs`: Vacuum virtual pairs (QOC); returns `{pairs_count, rate}` and emits PCO header `X-CERTEUS-PCO-qoc.vacuum_pairs.rate`.
- POST `/v1/qoc/energy_debt`: Helper to calculate energy debt for a number of pairs: `{pairs_count, mean_energy}` → `{energy_debt}`.

- POST `/v1/devices/horizon_drive/plan`: HDE planner; returns `plan_of_evidence`, `cost_tokens`, `expected_kappa`, and `alternatives[]` with `best_strategy`. Supports idempotency via `X-Idempotency-Key`; replay flagged by `X-Idempotent-Replay: 1`.
- POST `/v1/devices/qoracle/expectation`: Q‑Oracle expectation (heuristic distribution); returns `{optimum, payoff, distribution[]}`.
- POST `/v1/devices/entangle`: Entangler; returns `{certificate, achieved_negativity}` and exposes negativity metrics per variable.
- POST `/v1/devices/chronosync/reconcile`: Chronosync; returns `{reconciled, sketch}` with treaty clause skeleton.

## Billing & Cost‑tokens (T14)

- GET `/v1/billing/quota`: returns `{tenant, balance}`; tenant inferred from `X-Tenant-ID`/`X-Org-ID`
- POST `/v1/billing/quota`: body `{tenant?, units}` sets quota for tenant (demo‑admin)
- POST `/v1/billing/allocate`: body `{cost_units}` → `{status: "ALLOCATED"|"PENDING", tenant, balance}`
- POST `/v1/billing/refund`: body `{units}` → `{ok, tenant, balance}`

## Examples

- HDE — plan of evidence

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/devices/horizon_drive/plan \
  -H 'Content-Type: application/json' \
  -d '{
        "case": "demo-lex-001",
        "target_horizon": 0.30
      }'
```

Response (example):

```
{
  "evidence_plan": [
    {"action": "collect_email_evidence", "weight": 0.4},
    {"action": "request_affidavit", "weight": 0.6}
  ],
  "plan_of_evidence": [
    {"action": "collect_email_evidence", "weight": 0.4},
    {"action": "request_affidavit", "weight": 0.6}
  ],
  "cost_tokens": 60,
  "expected_kappa": 0.012,
  "alternatives": [
    {"strategy": "balanced", "cost_tokens": 60, "expected_kappa": 0.012},
    {"strategy": "aggressive", "cost_tokens": 84, "expected_kappa": 0.0132}
  ],
  "best_strategy": "balanced"
}
```

- Q‑Oracle — expectation

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/devices/qoracle/expectation \
  -H 'Content-Type: application/json' \
  -d '{
        "question": "Czy iść w wariant A?",
        "constraints": {"budget": 100}
      }'
```

Response (example):

```
{
  "optimum": {"choice": "A", "reason": "Czy iść w wariant A?"},
  "payoff": 0.6,
  "distribution": [
    {"outcome": "A", "p": 0.6},
    {"outcome": "B", "p": 0.4}
  ]
}
```

- QTMP — measure, sequence, decoherence, presets

```
# Initialize case predistribution (optional)
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/init_case \
  -H 'Content-Type: application/json' \
  -d '{"case":"demo-qtm-1","basis":["ALLOW","DENY","ABSTAIN"],"state_uri":"psi://uniform"}'

# Configure decoherence for case
=======
## QTMP — Examples

- Initialize case predistribution

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/init_case \
  -H 'Content-Type: application/json' \
  -d '{"case":"demo-qtm-1","basis":["ALLOW","DENY","ABSTAIN"],"state_uri":"psi://uniform"}'
```

- Configure decoherence

```
>>>>>>> origin/a4/weekly-20250905
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/decoherence \
  -H 'Content-Type: application/json' \
  -d '{"case":"demo-qtm-1","channel":"dephasing","gamma":0.2}'
<<<<<<< HEAD

# Single measurement (PCO headers include collapse event/priorities)
=======
```

- Single measurement (PCO headers in response)

```
>>>>>>> origin/a4/weekly-20250905
curl -i -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/measure \
  -H 'Content-Type: application/json' \
  -d '{"operator":"L","source":"ui","case":"demo-qtm-1"}' | sed -n '1,30p'
<<<<<<< HEAD

# Sequence of operators
=======
```

- Sequence of operators

```
>>>>>>> origin/a4/weekly-20250905
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/measure_sequence \
  -H 'Content-Type: application/json' \
  -d '{"operators":["L","T","W"],"case":"demo-qtm-1"}'
<<<<<<< HEAD

# Preset preferred operator for a case
=======
```

- Presets

```
>>>>>>> origin/a4/weekly-20250905
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/preset \
  -H 'Content-Type: application/json' \
  -d '{"case":"demo-qtm-1","operator":"T"}'

curl -sS http://127.0.0.1:8000/v1/qtm/presets
```

<<<<<<< HEAD
- lexqft — coverage update/state

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/lexqft/coverage/update \
  -H 'Content-Type: application/json' \
  -d '[
        {"gamma": 0.93, "weight": 1.0, "uncaptured": 0.03},
        {"gamma": 0.97, "weight": 2.0, "uncaptured": 0.01}
      ]'

curl -sS http://127.0.0.1:8000/v1/lexqft/coverage/state
```

- lexqft — tunneling

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/lexqft/tunnel \
  -H 'Content-Type: application/json' \
  -d '{"state_uri": "lexqft-case-1", "evidence_energy": 1.2}' -i | sed -n '1,20p'
```

Z modelem bariery (`barrier_model.energy` oraz opcjonalnie `model_uri`):

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/lexqft/tunnel \
  -H 'Content-Type: application/json' \
  -d '{
        "state_uri": "lexqft-case-1",
        "evidence_energy": 1.0,
        "barrier_model": {"energy": 1.5, "model_uri": "lexqft://barrier/demo"}
      }' -i | sed -n '1,20p'
```

- QOC — vacuum pairs

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qoc/vacuum_pairs \
  -H 'Content-Type: application/json' \
  -d '{"vacuum_energy": 2.0, "horizon_scale": 1.2}' -i | sed -n '1,20p'
```

- FIN→LexQFT coverage feed (implicit)

Wywołanie `/v1/fin/alpha/measure` dokłada wkład do agregatora pokrycia (gamma/uncaptured) w lexqft, co zasila Path‑Coverage Gate danymi FIN.

Log tunelowania (lekki): każde wywołanie `/v1/lexqft/tunnel` dopisuje wpis do `data/lexqft_tunnel_log.jsonl` z `{ts, case_id, barrier_energy, p_tunnel, path, counter_arguments[]}`.

- Entangle — negativity certificate

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/devices/entangle \
  -H 'Content-Type: application/json' \
  -d '{"variables": ["X", "Y", "Z"], "target_negativity": 0.2, "scenario": "pairwise"}'
```

- Chronosync — reconcile

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/devices/chronosync/reconcile \
  -H 'Content-Type: application/json' \
  -d '{
        "coords": {"timeline": "v2", "node": "A"},
        "pc_delta": {"doc1": "+hash"},
        "protocol": "mediation.v1"
      }'

- Billing — quota / allocate / refund

```

TENANT=t-demo
curl -sS http://127.0.0.1:8000/v1/billing/quota -H "X-Tenant-ID: $TENANT"
curl -sS -X POST http://127.0.0.1:8000/v1/billing/quota -H 'content-type: application/json' -d '{"tenant":"t-demo","units":3}'
curl -sS -X POST http://127.0.0.1:8000/v1/billing/allocate -H 'content-type: application/json' -H "X-Tenant-ID: $TENANT" -d '{"cost_units":2}'
curl -sS -X POST http://127.0.0.1:8000/v1/billing/allocate -H 'content-type: application/json' -H "X-Tenant-ID: $TENANT" -d '{"cost_units":2}'
curl -sS -X POST http://127.0.0.1:8000/v1/billing/refund -H 'content-type: application/json' -H "X-Tenant-ID: $TENANT" -d '{"units":1}'

```

```

### Packs — examples

```
# List packs
curl -sS http://127.0.0.1:8000/v1/packs/

# Try demo_report_pl
curl -sS -X POST \
  http://127.0.0.1:8000/v1/packs/try \
  -H 'Content-Type: application/json' \
  -d '{
        "pack": "demo_report_pl",
        "kind": "summarize",
        "payload": {"title": "My Report", "items": [1,2,3,4]}
      }'

# Install (requires hex(64+) signature)
curl -sS -X POST \
  http://127.0.0.1:8000/v1/packs/install \
  -H 'Content-Type: application/json' \
  -d '{"pack":"demo_billing_pl","signature":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","version":"1.0.0"}'

# Idempotent Devices example
curl -sS -X POST \
  http://127.0.0.1:8000/v1/devices/horizon_drive/plan \
  -H 'Content-Type: application/json' \
  -H 'X-Idempotency-Key: demo-123' \
  -d '{"target_horizon":0.25}' -i | sed -n '1,20p'
```

### Billing Tokens — examples

```
RID=$(curl -sS -X POST http://127.0.0.1:8000/v1/fin/tokens/request \
  -H 'Content-Type: application/json' \
  -d '{"user_id":"u123","amount":50,"purpose":"compute"}' | jq -r .request_id)

curl -sS http://127.0.0.1:8000/v1/fin/tokens/$RID

curl -sS -X POST http://127.0.0.1:8000/v1/fin/tokens/allocate \
  -H 'Content-Type: application/json' \
  -d '{"request_id":"'$RID'","allocated_by":"ops"}'

curl -sS http://127.0.0.1:8000/v1/fin/tokens/$RID
```

## SEC‑PCO (extension) — sample

Minimal extension payload for security findings (validated when `VALIDATE_PCO=1`):

```
{
  "security": {
    "finding_id": "SEC-0001",
    "severity": "HIGH",
    "status": "OPEN",
    "controls": ["ISO27001:A.12.6"],
    "evidence": [
      {
        "digest": "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "type": "artifact",
        "uri": "pfs://mail/MSEC/rep.pdf"
      }
    ],
    "cwe": ["CWE-79"],
    "cve": ["CVE-2025-0001"],
    "cvss": 8.2
  }
}
```

Schema: `schemas/security_pco_v0.1.json`. Evidence URIs use ProofFS (`pfs://…`) and can be checked via `/v1/pfs/exists`.

## CFE — Geometry of Meaning

- GET `/v1/cfe/curvature`: telemetry stub `{kappa_max}` (feeds Gauge‑Gate)
- POST `/v1/cfe/geodesic`: deterministic stub `{path[], geodesic_action, subject?}`; sets `X-CERTEUS-PCO-cfe.geodesic_action` and writes to Ledger
- POST `/v1/cfe/horizon`: body `{case?, lock?, domain?, severity?}` → `{locked, horizon_mass}`; sets `X-CERTEUS-PCO-cfe.horizon_mass` and writes to Ledger. Heurystyka: `lock=true` lub (domain∈{MED/SEC/CODE/FIN} ∧ severity∈{high/critical}) lub `case` zawiera `sample/przyklad`.
- GET `/v1/cfe/lensing?domain=LEX|FIN|MED|SEC|CODE`: domain‑aware influence map `{lensing_map{}, critical_precedents[], domain}`

Examples:

```
curl -sS "http://127.0.0.1:8000/v1/cfe/lensing?domain=MED" | jq

curl -sS -X POST \
  http://127.0.0.1:8000/v1/cfe/horizon \
  -H 'Content-Type: application/json' \
  -d '{"case":"MED-CASE-CRIT-1","domain":"MED","severity":"critical"}' -i | sed -n '1,20p'
```
=======
### QTMP — PCO headers

- `X-CERTEUS-PCO-qtm.collapse_event`: JSON with `operator`, `verdict`, `channel`.
- `X-CERTEUS-PCO-qtm.predistribution[]`: JSON array with predistribution for the case basis.
- `X-CERTEUS-PCO-qtmp.priorities`: JSON map of operator priorities `{W,I,C,L,T}`.
- `X-CERTEUS-PCO-correlation.cfe_qtmp`: scalar correlation between CFE and QTMP.
- `X-CERTEUS-PCO-qtm.collapse_prob`: probability of the selected verdict (float).
- `X-CERTEUS-PCO-qtm.collapse_latency_ms`: collapse latency in milliseconds (float).
>>>>>>> origin/a4/weekly-20250905
