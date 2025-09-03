#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/sdk/publish_ts_sdk.sh                        |
# | ROLE: Project script.                                        |
# | PLIK: scripts/sdk/publish_ts_sdk.sh                        |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+
set -euo pipefail
cd "$(dirname "$0")/../../clients/typescript/certeus-sdk"
if command -v npm >/dev/null 2>&1; then
  npm version patch --no-git-tag-version >/dev/null
  npm publish --access public
else
  echo "npm not found; please run in a Node.js environment" >&2
  exit 1
fi
