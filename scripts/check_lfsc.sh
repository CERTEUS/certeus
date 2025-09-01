#!/usr/bin/env bash
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE / PLIK: scripts/check_lfsc.sh                                  |
# | ROLA / ROLE: LFSC checker (Linux/CI).                               |
# | OPIS / DESC: Presence & signature; optional cvc5/lfsc-checker       |
# |             if SMT2 exists.                                         |
# +=====================================================================+
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

set -Eeuo pipefail

ART_DIR="${ART_DIR:-proof_artifacts}"
LFSC_NAME="${LFSC_NAME:-cvc5.lfsc}"
SHA_FILE="${SHA_FILE:-}"
SMT2_PATH="${SMT2_PATH:-}"

while getopts ":d:f:s:" opt; do
  case "$opt" in
    d) ART_DIR="$OPTARG" ;;
    f) LFSC_NAME="$OPTARG" ;;
    s) SHA_FILE="$OPTARG" ;;
    *) echo "Usage: $0 [-d artifacts_dir] [-f lfsc_file] [-s sha256sum_file]" >&2; exit 2 ;;
  esac
done

LFSC_PATH="${ART_DIR}/${LFSC_NAME}"
[[ -f "$LFSC_PATH" ]] || { echo "::error::LFSC not found: ${LFSC_PATH}"; exit 1; }
[[ -s "$LFSC_PATH" ]] || { echo "::error::LFSC is empty: ${LFSC_PATH}"; exit 1; }

# Optional SHA check
if [[ -n "${SHA_FILE}" ]]; then
  [[ -f "${SHA_FILE}" ]] || { echo "::error::SHA file not found: ${SHA_FILE}"; exit 1; }
  sha256sum -c "${SHA_FILE}" || { echo "::error::SHA256 mismatch for ${LFSC_PATH}"; exit 1; }
fi

# Signature sanity
grep -q 'PROOF' "$LFSC_PATH"       || { echo "::error file=${LFSC_PATH}::Missing PROOF signature"; exit 3; }
grep -q 'format=lfsc' "$LFSC_PATH" || { echo "::error file=${LFSC_PATH}::Missing format=lfsc"; exit 3; }

# External checker (optional)
if command -v cvc5 >/dev/null 2>&1; then
  if [[ -n "${SMT2_PATH}" && -f "${SMT2_PATH}" ]]; then
    echo "ℹ️ cvc5: SMT2 found → attempting proof check."
    cvc5 --proof-mode=lfsc --check-proofs "${SMT2_PATH}" >/dev/null || { echo "::error::cvc5 proof check failed"; exit 4; }
  else
    echo "ℹ️ cvc5 available, but SMT2 missing → skipping external verification."
  fi
elif command -v lfsc-checker >/dev/null 2>&1; then
  echo "ℹ️ lfsc-checker found; running…"
  lfsc-checker "${LFSC_PATH}" || { echo "::error::lfsc-checker failed"; exit 4; }
else
  echo "ℹ️ no LFSC checker found; basic checks only."
fi

echo "✅ LFSC check passed for ${LFSC_PATH}"
