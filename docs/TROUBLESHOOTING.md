# Troubleshooting

Common issues and where to look.

## API doesn’t start

- Check Python env and dependencies
- Inspect logs for binding/port conflicts
- Validate config: [configuration.md](configuration.md)

## Proofs are rejected at boundary

- Verify enforcement flags (STRICT_PROOF_ONLY, policy gates)
- Check gate logs and run relevant runbooks

## Observability metrics missing

- Ensure exporters are enabled and endpoints reachable
- See: [observability/quickstart.md](observability/quickstart.md)

## Useful Runbooks

- Boundary stuck: [runbooks/boundary-stuck.md](runbooks/boundary-stuck.md)
- PFS smoke: [runbooks/pfs_smoke.md](runbooks/pfs_smoke.md)
- Gauge drift: [runbooks/gauge-drift.md](runbooks/gauge-drift.md)
- Security hardening: [runbooks/security_hardening.md](runbooks/security_hardening.md)

If the issue persists, please open a GitHub issue with logs and steps to
reproduce.

