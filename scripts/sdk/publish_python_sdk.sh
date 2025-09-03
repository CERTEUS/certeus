#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/sdk/publish_python_sdk.sh                    |
# | ROLE: Project script.                                        |
# | PLIK: scripts/sdk/publish_python_sdk.sh                    |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+
set -euo pipefail
cd "$(dirname "$0")/../../clients/python/certeus_sdk"
python -m pip install -U twine >/dev/null
if [ ! -d dist ]; then
  echo "dist/ not found; building..." >&2
  python -m pip install -U build >/dev/null
  python -m build
fi
# Requires environment variables TWINE_USERNAME / TWINE_PASSWORD or .pypirc
twine upload dist/*
