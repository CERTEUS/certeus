#!/usr/bin/env bash
set -euo pipefail

# Uruchamia dowolne polecenie z ustawionymi GITHUB_TOKEN/GH_TOKEN
# pozyskanymi przez GitHub App. Jeśli jest dostępny `gh`, loguje sesję.
#
# Użycie:
#   tools/with-gh.sh <polecenie> [args...]
#   tools/with-gh.sh gh repo list

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

if [[ $# -lt 1 ]]; then
  echo "Użycie: $0 <polecenie> [args...]" >&2
  exit 2
fi

# Załaduj token i eksportuj
eval "$("${SCRIPT_DIR}/gh_app_token.sh" --export)"

# Opcjonalne zalogowanie gh CLI
if command -v gh >/dev/null 2>&1; then
  if ! gh auth status >/dev/null 2>&1; then
    printf '%s' "${GITHUB_TOKEN}" | gh auth login --with-token >/dev/null 2>&1 || true
  fi
fi

exec "$@"
