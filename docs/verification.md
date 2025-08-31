# Proof Verification Guide (LFSC/DRAT)

This guide explains how Proof verification hooks work and how to enable external verifiers for LFSC and DRAT, with configuration knobs and troubleshooting steps.

## Overview

- The API Gateway validates ProofBundle (v0.2) structure and performs light proof checks (heuristic) for LFSC/DRAT.
- You can enable external, real verifiers via environment variables for stronger guarantees.
- Failures increment SLO metrics (`certeus_proof_verification_failed_total`) and may result in ABSTAIN (fail‑closed path), per Manifest v1.7.

## External Verifiers

- LFSC (e.g., cvc5): set `CVC5_CMD` to the command that validates LFSC from stdin.
  - Example: `CVC5_CMD="cvc5 --proof-check --input-language=lfsc -"`
- DRAT checker: set `DRAT_CHECK_CMD` to the checker command that reads DRAT from stdin.
  - Example: `DRAT_CHECK_CMD="drat-trim -q -"` (or any compatible checker).
- Optional timeout for both: `PROOF_VERIFY_TIMEOUT_SECS` (default 10 seconds).

When these are set, the service will:
- Pipe LFSC/DRAT text to the given command via stdin
- Consider exit code 0 as success; non‑zero as failure
- Record a best‑effort detail in the verification result (including `rc` or error info)

If the commands are not set, the system uses a safe heuristic fallback (format signatures). Fallback may be looser; for enforcement, prefer real verifiers.

## Mocks (DEV/Tests)

To simulate outcomes without external tools, use `PROOF_VERIFIER_MOCK`:
- `lfsc_ok` or `lfsc_fail` — force LFSC result
- `drat_ok` or `drat_fail` — force DRAT result

This is useful for CI or local dev where installing verifiers is not practical.

## Integration Points

- Code: `services/proof_verifier/verifier.py`
  - `verify_lfsc(text)` and `verify_drat(text)` accept text, try external tools, fallback to heuristics, expose mocks.
- Manifest policy coupling:
  - ProofGate enforces policy thresholds and structural checks (derivations/solvers/formats) and may ABSTAIN if verification fails.
  - Metrics: `certeus_proof_verification_failed_total` increments on failures (visible at `/metrics`).

## Configuration Examples

- Shell (Linux/macOS):
```
export CVC5_CMD="cvc5 --proof-check --input-language=lfsc -"
export DRAT_CHECK_CMD="drat-trim -q -"
export PROOF_VERIFY_TIMEOUT_SECS=15
```

- PowerShell (Windows):
```
$env:CVC5_CMD = "cvc5 --proof-check --input-language=lfsc -"
$env:DRAT_CHECK_CMD = "drat-trim -q -"
$env:PROOF_VERIFY_TIMEOUT_SECS = "15"
```

- Docker Compose (dev‑stack): add to `infra/docker-compose.dev-stack.yml` under the `api` service:
```
    environment:
      CVC5_CMD: "cvc5 --proof-check --input-language=lfsc -"
      DRAT_CHECK_CMD: "drat-trim -q -"
      PROOF_VERIFY_TIMEOUT_SECS: "15"
```

## Troubleshooting

- External tool not found:
  - Verify the command is installed in PATH inside the runtime container/host.
  - Print `which cvc5` or `drat-trim` in the same shell/context where the API runs.
- Timeouts:
  - Increase `PROOF_VERIFY_TIMEOUT_SECS` for very large proofs.
- High `certeus_proof_verification_failed_total`:
  - Inspect logs and return codes; ensure inputs (LFSC/DRAT) are formatted for the given tool.
- ABSTAIN decisions:
  - Per Manifest v1.7, ProofGate prefers fail‑closed; ensure policy prerequisites (sources/derivations/repro/counsel) are met and verification passes.

