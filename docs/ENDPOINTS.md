# CERTEUS — Endpoints (MVP)

- POST `/v1/pco/bundle`: Build + validate ProofBundle v0.2; optional SMT2 verification; writes public payload.
- GET `/pco/public/{case_id}`: Public PCO (zero PII); validates Merkle path and Ed25519 signature.
- GET `/.well-known/jwks.json`: JWKS with Ed25519 public key.
- GET `/metrics`: Prometheus metrics (SLOs and counters).
- POST `/v1/sources/cache`: Cache a legal source (digest + path + retrieved_at).
- POST `/v1/proofgate/publish`: Policy-based decision (PUBLISH/CONDITIONAL/PENDING/ABSTAIN).

See also `docs/openapi/certeus.v1.yaml` for full schemas and examples.

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
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/decoherence \
  -H 'Content-Type: application/json' \
  -d '{"case":"demo-qtm-1","channel":"dephasing","gamma":0.2}'
```

- Single measurement (PCO headers in response)

```
curl -i -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/measure \
  -H 'Content-Type: application/json' \
  -d '{"operator":"L","source":"ui","case":"demo-qtm-1"}' | sed -n '1,30p'
```

- Sequence of operators

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/measure_sequence \
  -H 'Content-Type: application/json' \
  -d '{"operators":["L","T","W"],"case":"demo-qtm-1"}'
```

- Presets

```
curl -sS -X POST \
  http://127.0.0.1:8000/v1/qtm/preset \
  -H 'Content-Type: application/json' \
  -d '{"case":"demo-qtm-1","operator":"T"}'

curl -sS http://127.0.0.1:8000/v1/qtm/presets
```

### QTMP — PCO headers

- `X-CERTEUS-PCO-qtm.collapse_event`: JSON with `operator`, `verdict`, `channel`.
- `X-CERTEUS-PCO-qtm.predistribution[]`: JSON array with predistribution for the case basis.
- `X-CERTEUS-PCO-qtmp.priorities`: JSON map of operator priorities `{W,I,C,L,T}`.
- `X-CERTEUS-PCO-correlation.cfe_qtmp`: scalar correlation between CFE and QTMP.
- `X-CERTEUS-PCO-qtm.collapse_prob`: probability of the selected verdict (float).
- `X-CERTEUS-PCO-qtm.collapse_latency_ms`: collapse latency in milliseconds (float).
