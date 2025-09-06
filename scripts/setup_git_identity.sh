#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/setup_git_identity.sh                         |
# | ROLE: Ensure global git identity consistently               |
# +-------------------------------------------------------------+

set -euo pipefail

name="${GIT_USER_NAME:-}"
email="${GIT_USER_EMAIL:-}"

if [ -z "$name" ] && [ -f .devkeys/github_user.txt ]; then
  name=$(sed -n '1p' .devkeys/github_user.txt | tr -d '\r\n')
fi
if [ -z "$email" ] && [ -f .devkeys/github_email.txt ]; then
  email=$(sed -n '1p' .devkeys/github_email.txt | tr -d '\r\n')
fi

# Fallback: keep existing if present
cur_name=$(git config --global --get user.name || true)
cur_email=$(git config --global --get user.email || true)

if [ -n "$name" ]; then
  git config --global user.name "$name"
fi
if [ -n "$email" ]; then
  git config --global user.email "$email"
fi

echo "git user.name: $(git config --global --get user.name || echo '<unset>')"
echo "git user.email: $(git config --global --get user.email || echo '<unset>')"

