#!/usr/bin/env bash
set -euo pipefail

# Klonuje repozytorium z użyciem access tokena instalacji GitHub App
# Użycie:
#   tools/clone-repo.sh owner/repo [ścieżka_docelowa]

if [[ $# -lt 1 ]]; then
  echo "Użycie: $0 owner/repo [ścieżka_docelowa]" >&2
  exit 2
fi

FULL_NAME="$1"; shift || true
TARGET_DIR="${1:-}"

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

# Pobierz token i ustaw env
eval "$("${SCRIPT_DIR}/gh_app_token.sh" --export)"

REPO_URL="https://x-access-token:${GITHUB_TOKEN}@github.com/${FULL_NAME}.git"

if [[ -n "${TARGET_DIR}" ]]; then
  git clone "${REPO_URL}" "${TARGET_DIR}"
else
  git clone "${REPO_URL}"
fi
