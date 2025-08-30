# Konfiguracja / ENV — CERTEUS

Poniżej lista kluczowych zmiennych środowiskowych (ENV) i ich rola.

- STRICT_PROOF_ONLY: "1" aby wymusić Proof‑Only I/O (ingress)
- PCO_JWKS_B64URL: JWKS (JSON) w Base64URL z kluczem OKP/Ed25519 (publik) do weryfikacji tokenów
- ED25519_PUBKEY_B64URL: alternatywa — surowy klucz publiczny Ed25519 (Base64URL)
- ED25519_SECRET_B64URL: sekret Ed25519 (Base64URL) do podpisywania tokenów po stronie klienta (egress)
- GAUGE_EPSILON: próg gate’u Gauge (domyślnie 1e-3)
- PATH_COV_MIN_GAMMA: minimalne coverage_gamma (domyślnie 0.90)
- PATH_COV_MAX_UNCAPTURED: maksymalny uncaptured_mass (domyślnie 0.05)
- SLO_MAX_P95_MS: próg p95 latencji (domyślnie 250)
- SLO_MAX_ERROR_RATE: maksymalny error-rate (domyślnie 0.005)
- PROOF_BUNDLE_DIR: katalog z publicznymi bundlami PCO (domyślnie data/public_pco)
- CER_BASE: bazowy adres Gateway (np. http://localhost:8081)

Uwaga: dla środowisk CI (GitHub Actions) kroki cosign używają trybu keyless. Weryfikacja artefaktów odbywa się przez `cosign verify-blob` na parach (plik, .sig, .cert).
