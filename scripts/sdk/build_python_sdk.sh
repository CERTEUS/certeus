#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/sdk/build_python_sdk.sh                      |
# | ROLE: Project script.                                        |
# | PLIK: scripts/sdk/build_python_sdk.sh                      |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+
set -euo pipefail
cd "$(dirname "$0")/../../clients/python/certeus_sdk"
python -m pip install -U build >/dev/null
python -m build
echo "Built wheel/sdist under clients/python/certeus_sdk/dist/"
