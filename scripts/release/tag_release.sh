#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/release/tag_release.sh                       |
# | ROLE: Project script.                                        |
# | PLIK: scripts/release/tag_release.sh                       |
# | ROLA: Tagowanie wydania i push tagu.                         |
# +-------------------------------------------------------------+

set -euo pipefail

VER=${1:-v1.0.0}

echo "Creating annotated tag $VER"
git tag -a "$VER" -m "Release $VER"

echo "Pushing tag $VER"
git push origin "$VER"

echo "Done."

