#!/usr/bin/env markdown

# ADR-0001: Proof-Only I/O (PCO Required on Protected Endpoints)

- Status: Accepted
- Deciders: Core team
- Date: 2025-09-02

Context

- Some endpoints mutate or publish artifacts. To prevent unauthenticated or unverifiable writes, we require a Proof-Carrying Object (PCO) token (Ed25519 JWS) on protected routes.

Decision

- Enforce middleware in `services/api_gateway/security.attach_proof_only_middleware` on POST to protected paths.
- Invalid or missing token → 403 "DROP: proof-required".

Consequences

- Tests cover DROP on missing token.
- Improves auditability and integrity of publish-like flows.

References

- services/api_gateway/security.py
- tests/security/test_proof_only_middleware.py
