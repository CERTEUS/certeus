#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/dev_env.sh                                  |
# | ROLE: Shell script.                                         |
# | PLIK: scripts/dev_env.sh                                  |
# | ROLA: Skrypt powłoki.                                       |
# +-------------------------------------------------------------+
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
# CERTEUS — Developer environment bootstrap (Linux/macOS)
#
# Usage:
#   source ./scripts/dev_env.sh

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

set -euo pipefail

# Allow all origins in dev (adjust as needed)
export ALLOW_ORIGINS="${ALLOW_ORIGINS:-*}"

# JWKS public key for /.well-known/jwks.json
# If not provided, set to 32 bytes of zeros (dev-safe placeholder)
if [[ -z "${ED25519_PUBKEY_B64URL:-}" && -z "${ED25519_PUBKEY_HEX:-}" ]]; then
  export ED25519_PUBKEY_HEX="0000000000000000000000000000000000000000000000000000000000000000"
fi

echo "DEV ENV:"
echo "  ALLOW_ORIGINS=${ALLOW_ORIGINS}"
echo "  ED25519_PUBKEY_B64URL set? " $([[ -n "${ED25519_PUBKEY_B64URL:-}" ]] && echo true || echo false)
echo "  ED25519_PUBKEY_HEX    set? " $([[ -n "${ED25519_PUBKEY_HEX:-}" ]] && echo true || echo false)

# ProofGate report-only validation of PCO extensions in dev
export VALIDATE_PCO="${VALIDATE_PCO:-1}"
echo "  VALIDATE_PCO          = ${VALIDATE_PCO} (report-only)"
