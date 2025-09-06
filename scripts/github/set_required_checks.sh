#!/usr/bin/env bash
set -euo pipefail

# Set required status checks for a branch using GitHub API via gh cli.
# Usage: GITHUB_REPOSITORY=OWNER/REPO BRANCH=main bash scripts/github/set_required_checks.sh

: "${GITHUB_REPOSITORY:?Set GITHUB_REPOSITORY (OWNER/REPO)}"
BRANCH="${BRANCH:-main}"

checks=(
  "ProofFS Self-Hosted / macOS ProofFS (self-hosted)"
  "ProofFS Self-Hosted / Windows Dokan (self-hosted)"
)

echo "[i] Setting required status checks on $GITHUB_REPOSITORY@$BRANCH"

# Fetch current contexts (ignore errors if protection absent)
set +e
current_json=$(gh api -H "Accept: application/vnd.github+json" \
  "/repos/$GITHUB_REPOSITORY/branches/$BRANCH/protection/required_status_checks" 2>/dev/null)
rc=$?
set -e

declare -A want
for c in "${checks[@]}"; do want["$c"]=1; done

contexts=()
if [ $rc -eq 0 ] && command -v jq >/dev/null 2>&1; then
  mapfile -t exist < <(echo "$current_json" | jq -r '.contexts[]?') || true
  for e in "${exist[@]:-}"; do
    [ -n "$e" ] || continue
    contexts+=("$e")
    unset 'want[$e]' || true
  done
fi
for k in "${!want[@]}"; do contexts+=("$k"); done

args=("-F" "strict=true")
for c in "${contexts[@]}"; do args+=("-f" "contexts[]=$c"); done

# Create/update required contexts
gh api -X PATCH -H "Accept: application/vnd.github+json" \
  "/repos/$GITHUB_REPOSITORY/branches/$BRANCH/protection/required_status_checks" \
  "${args[@]}"

echo "[✓] Required checks updated:"
printf '  - %s\n' "${contexts[@]}"
