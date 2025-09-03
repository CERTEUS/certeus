#!/usr/bin/env bash
set -euo pipefail

echo "[panic] Revoking tokens and disabling integrations"
echo "- Revoke GitHub App and fine-grained PATs in Settings -> Developer settings"
echo "- Rotate GH_RUNNER_TOKEN for self-hosted runners"
echo "- Remove credentials from .git-credentials and runners"

