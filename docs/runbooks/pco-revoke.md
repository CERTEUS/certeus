# Runbook: PCO revoke

1. `POST /v1/upn/revoke` (z Merkle-dowodem).
2. Zweryfikuj propagację do Ledger + Boundary.
3. Publikuj komunikat w ChatOps/MailOps (audit trail).
