#!/usr/bin/env bash
set -euo pipefail

# Generuje jednowierszowy pakiet sekretów do wklejenia w .control/remote-bot.secret
# Format: APP_ID:INSTALLATION_ID:BASE64_PEM
# Użycie:
#   tools/remote-bot/pack-secret.sh              # wypisze na stdout
#   tools/remote-bot/pack-secret.sh --write      # zapisze do .control/remote-bot.secret

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
get_repo_root() {
  if command -v git >/dev/null 2>&1; then
    if git -C "${SCRIPT_DIR}" rev-parse --show-toplevel >/dev/null 2>&1; then
      git -C "${SCRIPT_DIR}" rev-parse --show-toplevel
      return
    fi
  fi
  (cd "${SCRIPT_DIR}/../.." 2>/dev/null && pwd) || (cd "${SCRIPT_DIR}/.." 2>/dev/null && pwd)
}
REPO_ROOT="$(get_repo_root)"

# Załaduj .env jeśli jest
if [[ -f "${REPO_ROOT}/.env" ]]; then
  set -o allexport
  # shellcheck disable=SC1090
  source "${REPO_ROOT}/.env"
  set +o allexport
fi

WRITE=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --write) WRITE=1; shift ;;
    -h|--help) echo "Użycie: $0 [--write]"; exit 0 ;;
    *) echo "Nieznana opcja: $1" >&2; exit 2 ;;
  esac
done

: "${GH_APP_ID:?Ustaw GH_APP_ID w env/.env}"
: "${GH_APP_INSTALLATION_ID:?Ustaw GH_APP_INSTALLATION_ID w env/.env}"

get_b64() {
  if [[ -n "${GH_APP_PRIVATE_KEY_B64:-}" ]]; then
    printf '%s' "${GH_APP_PRIVATE_KEY_B64}" | tr -d '\n'
    return 0
  fi
  if [[ -n "${GH_APP_PRIVATE_KEY:-}" ]]; then
    printf '%s' "${GH_APP_PRIVATE_KEY}" | sed 's/\\n/\n/g' | base64 -w 0 2>/dev/null || base64 2>/dev/null
    return 0
  fi
  if [[ -n "${GH_APP_PRIVATE_KEY_PATH:-}" ]]; then
    base64 -w 0 <"${GH_APP_PRIVATE_KEY_PATH}" 2>/dev/null || base64 <"${GH_APP_PRIVATE_KEY_PATH}" 2>/dev/null
    return 0
  fi
  if [[ -f "${REPO_ROOT}/.control/keys/github-app-private-key.pem" ]]; then
    base64 -w 0 <"${REPO_ROOT}/.control/keys/github-app-private-key.pem" 2>/dev/null || base64 <"${REPO_ROOT}/.control/keys/github-app-private-key.pem" 2>/dev/null
    return 0
  fi
  echo "Brak klucza prywatnego. Ustaw GH_APP_PRIVATE_KEY(_B64) lub GH_APP_PRIVATE_KEY_PATH." >&2
  return 1
}

b64=$(get_b64)
line="${GH_APP_ID}:${GH_APP_INSTALLATION_ID}:${b64}"

if [[ $WRITE -eq 1 ]]; then
  mkdir -p "${REPO_ROOT}/.control"
  umask 077
  printf '%s\n' "${line}" >"${REPO_ROOT}/.control/remote-bot.secret"
  echo "Zapisano do .control/remote-bot.secret"
else
  printf '%s\n' "${line}"
fi
