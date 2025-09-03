# Marketplace Demo (W14)

Cel: Pokaż pełny przepływ podpisu manifestu, weryfikacji i instalacji wtyczki.

## Wymagania
- Klucz prywatny Ed25519 (PEM): `.devkeys/dev_ed25519.pem`
- Klucz publiczny w ENV: `ED25519_PUBKEY_B64URL` (base64url bez `=`)
- API: `services.api_gateway.main:app`

## Krok 1 — Podpisz manifest (lokalnie)

```
$py scripts/marketplace/sign_manifest.py --in plugins/demo_alpha/plugin.yaml \
  --key .devkeys/dev_ed25519.pem --embed
```

Plik `plugins/demo_alpha/plugin.yaml` zyska linię `signature: <b64u>`.

Uwaga: API weryfikuje podpis względem treści manifestu BEZ linii `signature:`.

## Krok 2 — Weryfikacja podpisu (API)

```
MAN=plugins/demo_alpha/plugin.yaml
SIG=$(cat "$MAN" | rg '^signature:' | awk '{print $2}')
UNSIGNED=$(sed '/^signature:/d' "$MAN")
curl -s -X POST http://127.0.0.1:8000/v1/marketplace/verify_manifest \
  -H 'Content-Type: application/json' \
  -d '{"manifest_yaml":'"$UNSIGNED"',"signature_b64u":"'"$SIG"'"}'
```

## Krok 3 — Instalacja/upgrade

```
UNSIGNED=$(sed '/^signature:/d' plugins/demo_alpha/plugin.yaml)
curl -s -X POST http://127.0.0.1:8000/v1/marketplace/install \
  -H 'Content-Type: application/json' \
  -d '{"name":"demo_alpha","manifest_yaml":'"$UNSIGNED"',"signature_b64u":"'"$SIG"'"}' | jq .
```

## Krok 4 — Lista zainstalowanych

```
curl -s http://127.0.0.1:8000/v1/marketplace/plugins | jq .
```

## Uwagi
- Weryfikacja używa `security.key_manager.load_ed25519_public_bytes` — klucz publiczny pobierany z ENV/Vault.
- Instalacja nadpisuje `plugins/<name>/plugin.yaml` treścią z żądania (po weryfikacji podpisu).
