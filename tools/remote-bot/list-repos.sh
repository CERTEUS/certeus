#!/usr/bin/env bash
set -euo pipefail

# Wypisuje repozytoria dostępne dla instalacji GitHub App
# Użycie:
#   tools/list-repos.sh

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

# Pobierz token i wywołaj API
eval "$("${SCRIPT_DIR}/gh_app_token.sh" --export)"

curl -sS -H "Authorization: token ${GITHUB_TOKEN}" \
  -H "Accept: application/vnd.github+json" \
  "https://api.github.com/installation/repositories?per_page=100" | \
  {
    if command -v jq >/dev/null 2>&1; then
      jq -r '.repositories[]?.full_name'
    else
      python3 - <<'PY'
import sys, json
data = json.load(sys.stdin)
for r in (data.get('repositories') or []):
    fn = r.get('full_name')
    if fn: print(fn)
PY
    fi
  }
