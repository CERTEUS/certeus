param()
$ErrorActionPreference = "Stop"
New-Item -ItemType Directory -Force -Path .devkeys | Out-Null
$py = "$PWD\.venv\Scripts\python.exe"
if (!(Test-Path $py)) { throw "Python venv not found: $py" }

# Generate a dev Ed25519 private key using Python (cryptography)
$code = @'
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
from pathlib import Path
p = Path('.devkeys'); p.mkdir(exist_ok=True)
k = Ed25519PrivateKey.generate()
pem = k.private_bytes(
    encoding=serialization.Encoding.PEM,
    format=serialization.PrivateFormat.PKCS8,
    encryption_algorithm=serialization.NoEncryption(),
)
(p / 'ed25519_priv.pem').write_bytes(pem)
'@
$tmp = Join-Path $env:TEMP ('certeus_gen_key_' + [System.Guid]::NewGuid().ToString('N') + '.py')
Set-Content -LiteralPath $tmp -Value $code -Encoding UTF8
try { & $py $tmp } finally { Remove-Item -LiteralPath $tmp -ErrorAction SilentlyContinue }

if (!(Test-Path .env)) { Set-Content .env "" -Encoding UTF8 }
$lines = Get-Content .env -ErrorAction SilentlyContinue
if ($lines -notmatch 'ED25519_PRIVKEY_PEM_PATH=') { Add-Content .env "ED25519_PRIVKEY_PEM_PATH=.devkeys\ed25519_priv.pem" }
if ($lines -notmatch 'PROOF_BUNDLE_DIR=') { Add-Content .env "PROOF_BUNDLE_DIR=data\public_pco" }
Write-Host "OK: wygenerowano .devkeys\ed25519_priv.pem i zaktualizowano .env"
