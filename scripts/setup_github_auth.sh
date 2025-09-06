#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/setup_github_auth.sh                          |
# | ROLE: Configure GitHub auth for seamless git push           |
# +-------------------------------------------------------------+

set -euo pipefail

msg() { printf "[github-auth] %s\n" "$*"; }
warn() { printf "[github-auth][warn] %s\n" "$*"; }

# Resolve home and credentials file
HOME_DIR=${HOME:-$(getent passwd "$(id -u)" | cut -d: -f6 || echo "/root")}
CRED_FILE="$HOME_DIR/.git-credentials"

# Try to discover username/token
USER_CAND="${GITHUB_USER:-${GH_USER:-${GIT_USER:-${USER:-}}}}"
TOKEN_CAND="${GITHUB_PUSH_TOKEN:-${GITHUB_TOKEN:-${GH_TOKEN:-${ADMIN_TOKEN:-}}}}"

# Local files (ignored by git)
# Sanitize common container usernames
case "${USER_CAND:-}" in
  vscode|root|codespace|code) USER_CAND="" ;;
esac

if [ -z "${USER_CAND}" ] && [ -f .devkeys/github_user.txt ]; then
  USER_CAND=$(sed -n '1p' .devkeys/github_user.txt | tr -d '\r\n')
fi
if [ -z "${TOKEN_CAND}" ]; then
  for f in .devkeys/admin_token.txt .devkeys/github_pat.txt .devkeys/token.txt; do
    if [ -f "$f" ]; then
      TOKEN_CAND=$(sed -n '1p' "$f" | tr -d '\r\n')
      break
    fi
  done
fi

# Try GitHub CLI token if available
if [ -z "${TOKEN_CAND}" ] && command -v gh >/dev/null 2>&1; then
  if gh auth status >/dev/null 2>&1; then
    TOKEN_CAND=$(gh auth token 2>/dev/null || true)
  fi
fi

if [ -z "${TOKEN_CAND}" ]; then
  warn "No token found. Provide one via env (GITHUB_PUSH_TOKEN/GITHUB_TOKEN/GH_TOKEN/ADMIN_TOKEN) or .devkeys/*.txt"
  warn "Alternatively, login via: gh auth login --hostname github.com --web --git-protocol https"
  exit 0
fi

# Resolve username from API if missing
if [ -z "${USER_CAND}" ]; then
  if command -v curl >/dev/null 2>&1; then
    USER_CAND=$(curl -fsSL -H "Authorization: token ${TOKEN_CAND}" https://api.github.com/user | sed -n 's/.*"login"\s*:\s*"\([^"]\+\)".*/\1/p' | head -n1 || true)
  fi
fi

# Fallback username for tokens
if [ -z "${USER_CAND}" ]; then
  USER_CAND="x-access-token"
fi

mkdir -p "${HOME_DIR}"

# Prepare host-level and repo-level entries (repo is inferred from origin when available)
HOST_LINE="https://${USER_CAND}:${TOKEN_CAND}@github.com"

REPO_LINE=""
if origin_url=$(git remote get-url origin 2>/dev/null); then
  REPO_LINE="https://${USER_CAND}:${TOKEN_CAND}@${origin_url#https://}"
fi

touch "$CRED_FILE"
chmod 0600 "$CRED_FILE" || true

# Idempotently append entries if not present
grep -qF "$HOST_LINE" "$CRED_FILE" || echo "$HOST_LINE" >> "$CRED_FILE"
if [ -n "$REPO_LINE" ]; then
  grep -qF "$REPO_LINE" "$CRED_FILE" || echo "$REPO_LINE" >> "$CRED_FILE"
fi

# Configure git to use stored credentials
git config --global credential.helper store
git config --global credential.useHttpPath true

msg "Configured git credential store at: $CRED_FILE"
msg "GitHub user: ${USER_CAND}"
msg "You can now run: git push"
