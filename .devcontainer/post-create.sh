#!/usr/bin/env bash
set -euo pipefail
python -m venv .venv
. .venv/bin/activate
python -m pip install -U pip wheel setuptools ruff pytest jsonschema cryptography fastapi uvicorn

# klucze DEV lokalnie w kontenerze (nie commitujemy)
mkdir -p .devkeys data/public_pco reports
python - << 'PY'
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
p = Ed25519PrivateKey.generate()
pem = p.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption())
open(".devkeys/ed25519_priv.pem","wb").write(pem)
PY
echo "ED25519_PRIVKEY_PEM_PATH=.devkeys/ed25519_priv.pem" >> .env
echo "PROOF_BUNDLE_DIR=data/public_pco" >> .env

# LFS i podstawy
git lfs install || true
ruff check . --fix || true
ruff format .
pytest -q || true
