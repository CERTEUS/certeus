# CHANGELOG — Certeus

## 2025-09-09 — Konsolidacja gałęzi i stabilizacja CI

- Polityka gałęzi: `main` + `work/daily`; usunięto stare gałęzie.
- CI: `Tests` uproszczone (pip + python); `ci-gates` na PR/main.
- Bramki: spójne flagi PQ/Bunker (`PQCRYPTO_REQUIRE`, `BUNKER`, `TEE_RA_REQUIRE`, `PROFILE=prod`).
- RAaaS i ZKP: realne implementacje + testy.
- Dema: deterministyczne `image_digest` (ENV/git/README fallback).
- OpenAPI: kontrakt zsynchronizowany; SDK/Docs korzystają z tej samej wersji.

