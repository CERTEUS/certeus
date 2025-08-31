# CERTEUS — Endpoints (MVP)

- POST `/v1/pco/bundle`: Build + validate ProofBundle v0.2; optional SMT2 verification; writes public payload.
- GET `/pco/public/{case_id}`: Public PCO (zero PII); validates Merkle path and Ed25519 signature.
- GET `/.well-known/jwks.json`: JWKS with Ed25519 public key.
- GET `/metrics`: Prometheus metrics (SLOs and counters).
- POST `/v1/sources/cache`: Cache a legal source (digest + path + retrieved_at).
- POST `/v1/proofgate/publish`: Policy-based decision (PUBLISH/CONDITIONAL/PENDING/ABSTAIN).

See also `docs/openapi/certeus.v1.yaml` for full schemas and examples.
