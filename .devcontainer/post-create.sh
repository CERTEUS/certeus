#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: .devcontainer/post-create.sh                        |
# | ROLE: Shell script.                                         |
# | PLIK: .devcontainer/post-create.sh                        |
# | ROLA: Skrypt powłoki.                                       |
# +-------------------------------------------------------------+
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
set -euo pipefail

# 1) Virtualenv + narzędzia
python -m venv .venv
. .venv/bin/activate
python -m pip install -U pip wheel setuptools

# 2) Zależności projektu dokładnie jak w CI
#    (instalacja edytowalna + requirements)
python -m pip install -e .
if [ -f requirements.txt ]; then
  python -m pip install -r requirements.txt
fi
#    Narzędzia deweloperskie/testowe używane w CI
python -m pip install -U ruff pytest pytest-xdist pytest-asyncio httpx z3-solver hypothesis openapi-spec-validator PyYAML

# 3) Pliki i zmienne środowiskowe dla DEV (niecommitowalne)
mkdir -p .devkeys data/public_pco reports
if [ ! -f .env ]; then
  # Zainicjuj z przykładu, o ile istnieje
  if [ -f .env.example ]; then
    cp .env.example .env
  else
    touch .env
  fi
fi
python - << 'PY'
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization
from pathlib import Path
Path('.devkeys').mkdir(parents=True, exist_ok=True)
p = Ed25519PrivateKey.generate()
pem = p.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption())
Path('.devkeys/ed25519_priv.pem').write_bytes(pem)
PY
grep -q '^ED25519_PRIVKEY_PEM_PATH=' .env || echo "ED25519_PRIVKEY_PEM_PATH=.devkeys/ed25519_priv.pem" >> .env
grep -q '^PROOF_BUNDLE_DIR=' .env || echo "PROOF_BUNDLE_DIR=data/public_pco" >> .env
# Ujednolicenie bramek PQ‑Crypto (jak w CI)
grep -q '^PQCRYPTO_REQUIRE=' .env || echo "PQCRYPTO_REQUIRE=0" >> .env
grep -q '^PQCRYPTO_READY=' .env   || echo "PQCRYPTO_READY=0" >> .env

# 4) Git LFS + szybkie sanity bez hałasu
git lfs install || true
# Nie uruchamiamy automatycznie testów ani formatowania, żeby nie produkować szumu przy starcie
echo "Devcontainer provisioning done. Activate venv: 'source .venv/bin/activate'"

# 5) Optional: Configure GitHub auth for seamless git push (if token provided)
if [ -f "scripts/setup_github_auth.sh" ]; then
  bash scripts/setup_github_auth.sh || true
fi

# 6) Enforce local git hooks (block secrets & enforce conv. commits)
git config core.hooksPath .githooks || true

# 7) Ensure global git identity (from .devkeys or env)
if [ -f "scripts/setup_git_identity.sh" ]; then
  bash scripts/setup_git_identity.sh || true
fi
