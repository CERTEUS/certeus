# Key Management — CERTEUS

- Default backend: ENV/files
  - Private: `ED25519_PRIVKEY_PEM` or `ED25519_PRIVKEY_PEM_PATH`
  - Public: `ED25519_PUBKEY_B64URL` or `ED25519_PUBKEY_HEX`
- Optional backend: Vault (KV v2)
  - Set `KEYS_BACKEND=vault`, `VAULT_ADDR`, `VAULT_TOKEN`, `VAULT_SECRET_PATH`
  - Expected fields: `ed25519_privkey_pem` (PEM), `ed25519_pubkey_b64url` (Base64URL)
- Rotation: write new secret version, reload service (or hot-reload JWKS if supported)
