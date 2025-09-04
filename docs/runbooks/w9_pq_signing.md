#!/usr/bin/env markdown

# W9 — PQ‑crypto (stub) podpis Merkle path

Endpointy:
- `POST /v1/pfs/sign_path {case, path[], sk_b64url?}` → `{merkle_root, signature_b64?}`
- `POST /v1/pfs/verify_path {case, path[], pk_b64url, signature_b64}` → `{ok}`

Przykład (Ed25519, base64url RAW kluczy):
1) Generuj parę kluczy (python/cryptography) lub użyj własnych w formacie RAW.
2) Podpis:
```
curl -s -X POST http://127.0.0.1:8000/v1/pfs/sign_path \
 -H 'Content-Type: application/json' \
 -d '{"case":"MERKLE","path":["lexqft.tunnel","cfe.geodesic","proof.publish"],"sk_b64url":"<SK_RAW_B64URL>"}'
```
3) Weryfikacja:
```
curl -s -X POST http://127.0.0.1:8000/v1/pfs/verify_path \
 -H 'Content-Type: application/json' \
 -d '{"case":"MERKLE","path":["lexqft.tunnel","cfe.geodesic","proof.publish"],"pk_b64url":"<PK_RAW_B64URL>","signature_b64":"<SIG_B64URL>"}'
```

Uwaga: to stub (nie ML‑DSA). Integracja PQ‑crypto możliwa przez `python-oqs` lub serwis zewn.
