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

See also `docs/openapi/certeus.v1.yaml` for full schemas and examples.

- GET `/v1/lexqft/coverage`: Aggregated path coverage gamma (`coverage_gamma`).
- GET `/v1/lexqft/coverage/state`: Coverage state with weighted `coverage_gamma` and `uncaptured_mass`.
- POST `/v1/lexqft/coverage/update`: Replace coverage contributions: `{gamma, weight, uncaptured}[]`.
- POST `/v1/lexqft/coverage/reset`: Reset coverage aggregator (clears persisted state).
- POST `/v1/lexqft/tunnel`: Tunneling heuristic; returns `{p_tunnel, min_energy_to_cross, path}` and emits PCO headers `X-CERTEUS-PCO-qlaw.tunneling.*`.

- POST `/v1/devices/horizon_drive/plan`: HDE planner; returns `plan_of_evidence`, `cost_tokens`, `expected_kappa`, and `alternatives[]` with `best_strategy`.
- POST `/v1/devices/qoracle/expectation`: Q‑Oracle expectation (heuristic distribution); returns `{optimum, payoff, distribution[]}`.
- POST `/v1/devices/entangle`: Entangler; returns `{certificate, achieved_negativity}` and exposes negativity metrics per variable.
- POST `/v1/devices/chronosync/reconcile`: Chronosync; returns `{reconciled, sketch}` with treaty clause skeleton.

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
```
