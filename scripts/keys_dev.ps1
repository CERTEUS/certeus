# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/keys_dev.ps1                                |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/keys_dev.ps1                                |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

param()
$ErrorActionPreference = "Stop"
New-Item -ItemType Directory -Force -Path .devkeys | Out-Null
# Resolve Python path: prefer local venv, fallback to uv-managed or PATH
function Resolve-Py {
  $local = Join-Path $PWD ".venv/\Scripts/python.exe"
  if (Test-Path $local) { return (Resolve-Path $local).Path }
  try { $cmd = Get-Command python -ErrorAction Stop; return $cmd.Source } catch {}
  $uv = Join-Path $env:USERPROFILE 'AppData/\Roaming/\uv/\python/\cpython-3.11.9-windows-x86_64-none/\python.exe'
  if (Test-Path $uv) { return $uv }
  throw "Python not found: expected .venv or uv-managed python"
}
$py = Resolve-Py

# Generate a dev Ed25519 private key using Python (cryptography)
$code = @'
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
from pathlib import Path
import base64

p = Path('.devkeys'); p.mkdir(exist_ok=True)
k = Ed25519PrivateKey.generate()
pem = k.private_bytes(
    encoding=serialization.Encoding.PEM,
    format=serialization.PrivateFormat.PKCS8,
    encryption_algorithm=serialization.NoEncryption(),
)
(p / 'ed25519_priv.pem').write_bytes(pem)
pub = k.public_key().public_bytes(
    encoding=serialization.Encoding.Raw,
    format=serialization.PublicFormat.Raw,
)
(p / 'ed25519_pub.hex').write_text(pub.hex(), encoding='utf-8')
(p / 'ed25519_pub.b64u').write_text(base64.urlsafe_b64encode(pub).rstrip(b'=').decode('ascii'), encoding='utf-8')
'@
$tmp = Join-Path $env:TEMP ('certeus_gen_key_' + [System.Guid]::NewGuid().ToString('N') + '.py')
Set-Content -LiteralPath $tmp -Value $code -Encoding UTF8
try { & $py $tmp } finally { Remove-Item -LiteralPath $tmp -ErrorAction SilentlyContinue }

if (!(Test-Path .env)) { Set-Content .env "" -Encoding UTF8 }
$lines = Get-Content .env -ErrorAction SilentlyContinue
if ($lines -notmatch 'ED25519_PRIVKEY_PEM_PATH=') { Add-Content .env "ED25519_PRIVKEY_PEM_PATH=.devkeys\ed25519_priv.pem" }
if ($lines -notmatch 'PROOF_BUNDLE_DIR=') { Add-Content .env "PROOF_BUNDLE_DIR=data\public_pco" }
if ($lines -notmatch 'ED25519_PUBKEY_HEX=') {
  $pubhex = Get-Content .devkeys\ed25519_pub.hex -Raw -ErrorAction SilentlyContinue
  if ($pubhex) { Add-Content .env ("ED25519_PUBKEY_HEX=" + ($pubhex.Trim())) }
}
if ($lines -notmatch 'ED25519_PUBKEY_B64URL=') {
  $pubb64u = Get-Content .devkeys\ed25519_pub.b64u -Raw -ErrorAction SilentlyContinue
  if ($pubb64u) { Add-Content .env ("ED25519_PUBKEY_B64URL=" + ($pubb64u.Trim())) }
}
# Użycie / Usage:
#   pwsh -File .\scripts\keys_dev.ps1
# Efekt:
#   - .devkeys/ed25519_priv.pem (klucz prywatny Ed25519)
#   - .devkeys/ed25519_pub.hex, .devkeys/ed25519_pub.b64u (klucz publiczny)
#   - dopisane do .env: PROOF_BUNDLE_DIR, ED25519_* (jeśli brakowało)
Write-Host "OK: wygenerowano .devkeys\ed25519_priv.pem i zaktualizowano .env"
