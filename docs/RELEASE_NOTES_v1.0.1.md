# RELEASE NOTES v1.0.1 — Konsolidacja gałęzi i stabilizacja CI

Data: 2025-09-09

Najważniejsze zmiany:

- Gałęzie: pozostawiono `main` + `work/daily` (jedna gałąź robocza); usunięto gałęzie poboczne.
- CI: `Tests` deterministyczny (pip + python); `ci-gates` na PR/main (enforce bramek bezpieczeństwa i jakości).
- Bramki PQ/Bunker: ujednolicone flagi (`PQCRYPTO_REQUIRE`, `BUNKER`, `TEE_RA_REQUIRE`, `PROFILE=prod`).
- RAaaS i ZKP: realne implementacje + testy (raas_service/main.py, zkp_service/stub.py, tests/*).
- Dema: deterministyczne `image_digest` (ENV/git/README fallback), brak placeholderów.
- OpenAPI: kontrakt zsynchronizowany (narzędzia w Control: `tools/openapi-sync.sh`).

Uwaga: workflowy na `main` wymagają zielonych statusów; patrz polityka PR poniżej.

