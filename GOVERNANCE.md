# CODEOWNERS & Maintainers

- Patrz `CODEOWNERS` i role.

## Policy Control Unit (PCU)

- Zmiany packów i progów TruthOps wymagają podpisów **m-of-n**.
- Rejestr packów: `policies/normative_registry/registry.jsonl` (append-only).

## Break-Glass

- **TTL ≤ 14 dni**, pełny log w Merkle.
- Operacje BG opisywane w `governance/pcu_breakglass.py`.

## Proof Gate

- Merge zablokowany bez zielonego DRAT/LFSC + walidatora packów.
