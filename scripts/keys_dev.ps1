param()
$ErrorActionPreference = "Stop"
New-Item -ItemType Directory -Force -Path .devkeys | Out-Null
$py = "$PWD\.venv\Scripts\python.exe"
& $py - << 'PYCODE'
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
from pathlib import Path
p = Path('.devkeys'); p.mkdir(exist_ok=True)
k = Ed25519PrivateKey.generate()
pem = k.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption())
open(p / 'ed25519_priv.pem', 'wb').write(pem)
PYCODE
if (!(Test-Path .env)) { Set-Content .env "" -Encoding UTF8 }
$lines = Get-Content .env -ErrorAction SilentlyContinue
if ($lines -notmatch 'ED25519_PRIVKEY_PEM_PATH=') { Add-Content .env "ED25519_PRIVKEY_PEM_PATH=.devkeys\ed25519_priv.pem" }
if ($lines -notmatch 'PROOF_BUNDLE_DIR=') { Add-Content .env "PROOF_BUNDLE_DIR=data\public_pco" }
Write-Host "OK: wygenerowano .devkeys\ed25519_priv.pem i zaktualizowano .env"

