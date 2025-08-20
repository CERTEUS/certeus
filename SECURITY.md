# Postura i zakres

- Minimalny przywilej, brak PII w PCO, E2E envelope opcjonalnie (AES-GCM, KMS).
- JWKS rotacja: ACTIVE/GRACE KID w okienku łaski; publikacja JWKS z cache headers.

## Łańcuch dostaw (SLSA/SBOM)

- SBOM generowany w CI; podpisy artefaktów.
- SLSA L3 (source provenance) – cele: build hermetyczny.

## Skany i bramki

- CodeQL, secret-scanning, dep scans (pip-audit). Merge blokuje „red” (Proof-Gate + security).

## Zgłaszanie podatności

- Bezpieczny kanał: security@… (PGP), SLA triage 48h, publikacja advisory.

## Klucze/KMS

- Rotacja KID (ACTIVE/GRACE), JWKS opublikowany. Break-Glass TTL ≤14 dni + Merkle-log.

## TTDE & DR

- Re-proof po TTL (prawo=365d, med=90d, fin=7d); DR game-day; immutable Merkle-ledger.

## Hardening

- CORS restrykcyjny na prod, izolacja /static/previews (attachment), rate limit/PoW na PCO.
