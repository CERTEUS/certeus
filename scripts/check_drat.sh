#!/usr/bin/env bash
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE / PLIK: scripts/check_drat.sh                                  |
# | ROLA / ROLE: DRAT checker (Linux/CI).                               |
# | OPIS / DESC: Presence & signature; optional drat-trim if CNF exists.|
# +=====================================================================+
set -Eeuo pipefail

ART_DIR="${ART_DIR:-proof_artifacts}"
DRAT_NAME="${DRAT_NAME:-z3.drat}"
SHA_FILE="${SHA_FILE:-}"
CNF_PATH="${CNF_PATH:-}"

while getopts ":d:f:s:" opt; do
  case "$opt" in
    d) ART_DIR="$OPTARG" ;;
    f) DRAT_NAME="$OPTARG" ;;
    s) SHA_FILE="$OPTARG" ;;
    *) echo "Usage: $0 [-d artifacts_dir] [-f drat_file] [-s sha256sum_file]" >&2; exit 2 ;;
  esac
done

DRAT_PATH="${ART_DIR}/${DRAT_NAME}"
[[ -f "$DRAT_PATH" ]] || { echo "::error::DRAT not found: ${DRAT_PATH}"; exit 1; }
[[ -s "$DRAT_PATH" ]] || { echo "::error::DRAT is empty: ${DRAT_PATH}"; exit 1; }

# Optional SHA check
if [[ -n "${SHA_FILE}" ]]; then
  [[ -f "${SHA_FILE}" ]] || { echo "::error::SHA file not found: ${SHA_FILE}"; exit 1; }
  sha256sum -c "${SHA_FILE}" || { echo "::error::SHA256 mismatch for ${DRAT_PATH}"; exit 1; }
fi

# Signature sanity
grep -q 'PROOF' "$DRAT_PATH"       || { echo "::error file=${DRAT_PATH}::Missing PROOF signature"; exit 3; }
grep -q 'format=drat' "$DRAT_PATH" || { echo "::error file=${DRAT_PATH}::Missing format=drat"; exit 3; }

# External checker (optional)
if command -v drat-trim >/dev/null 2>&1; then
  if [[ -n "${CNF_PATH}" && -f "${CNF_PATH}" ]]; then
    echo "ℹ️ drat-trim: CNF found → running verification…"
    drat-trim "${CNF_PATH}" "${DRAT_PATH}" -q || { echo "::error::drat-trim verification failed"; exit 4; }
  else
    echo "ℹ️ drat-trim available, but CNF missing → skipping external verification."
  fi
else
  echo "ℹ️ drat-trim not found; basic checks only."
fi

echo "✅ DRAT check passed for ${DRAT_PATH}"
