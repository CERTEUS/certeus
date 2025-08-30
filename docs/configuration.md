# Konfiguracja / ENV (CERTEUS)

| Zmienna               | Opis                                                 | Domyślna                |
| --------------------- | ---------------------------------------------------- | ----------------------- |
| `CER_PROOF_STRICT`    | Wymuszaj Proof-Only Sockets (brak PCO => DROP)       | `true`                  |
| `CER_BOUNDARY_BUCKET` | Lokalizacja WORM dla Boundary (np. s3://bucket/path) | –                       |
| `CER_CRYPTO_MODE`     | Tryb podpisu: `hybrid` (Ed25519+ML-DSA)              | `hybrid`                |
| `CER_TEE_REQUIRED`    | Wymuszaj profil Bunkier (TEE + RA)                   | `false`                 |
| `CER_BASE`            | Bazowy URL usług                                     | `http://localhost:8081` |

## Pliki

- `infra/docker-compose.dev.yml` – środowisko dev
- `infra/k8s/*.yaml` – manifesty k8s
- `clients/web/public/brand/*` – favicony, manifest
