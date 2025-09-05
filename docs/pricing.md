# Pricing & Limits (W17)

This document outlines the Proof‑Cost token model used in the dev/demo environment.

- Tiers (default policies):
  - free: daily_quota=200, burst=1.0
  - pro: daily_quota=10,000, burst=2.0
  - enterprise: daily_quota=250,000, burst=3.0

- Tenant mapping:
  - Unassigned tenants default to the "free" tier.
  - Mapping can be adjusted in `runtime/billing/policies.json` or via `BILLING_POLICY_FILE` env var.

- Runtime integration:
  - Endpoint `GET /v1/billing/policies` returns current policies (read‑only).
  - Endpoint `GET /v1/billing/tenant_tier` returns the current tenant tier.
  - Budget checks are enforced via `enforce_limits(request, cost_units=N)` in routers.

- Overrides:
  - `BILLING_POLICY_FILE=/path/to/policies.json` to point to a custom JSON.
  - Routes may charge different `cost_units` depending on complexity.

This is a baseline for dev/demo; production pricing and quotas are configured per deployment.

