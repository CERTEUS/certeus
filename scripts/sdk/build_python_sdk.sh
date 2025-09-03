#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../clients/python/certeus_sdk"
python -m pip install -U build >/dev/null
python -m build
echo "Built wheel/sdist under clients/python/certeus_sdk/dist/"

