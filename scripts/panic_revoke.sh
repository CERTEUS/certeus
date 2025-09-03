#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/panic_revoke.sh                               |
# | ROLE: Panic revoke helper (bash)                            |
# | PLIK: scripts/panic_revoke.sh                               |
# | ROLA: Skrypt odcięcia i rotacji sekretów                    |
# +-------------------------------------------------------------+

set -euo pipefail

echo "[panic] Revoking tokens and disabling integrations"
echo "- Revoke GitHub App and fine-grained PATs in Settings -> Developer settings"
echo "- Rotate GH_RUNNER_TOKEN for self-hosted runners"
echo "- Remove credentials from .git-credentials and runners"
