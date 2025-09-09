#!/usr/bin/env bash
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/prooffs/mount_ro.sh                         |
# | ROLE: Shell script.                                         |
# | PLIK: scripts/prooffs/mount_ro.sh                         |
# | ROLA: Skrypt powłoki.                                       |
# +-------------------------------------------------------------+
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

set -Eeuo pipefail
trap 'echo "[ERR] ${0##*/} line:${LINENO} status:$?" >&2' ERR

# CERTEUS • ProofFS (read-only) mount helper
# Usage:
#   scripts/prooffs/mount_ro.sh <SRC_DIR> <MOUNTPOINT>
#
# Linux (root):
#   mount --bind SRC MNT && mount -o remount,ro,bind MNT
# macOS:
#   mount -t nullfs -o ro SRC MNT
#
# Notes:
# - This helper prefers bind/nullfs mounts to keep dependencies minimal.
# - For a full FUSE driver, integrate with pfs-fuse sidecar (out of scope here).

usage() {
  cat <<'EOF'
Usage: mount_ro.sh <SRC_DIR> <MOUNTPOINT>
Mount SRC_DIR as read-only at MOUNTPOINT.

Examples:
  sudo bash scripts/prooffs/mount_ro.sh data/public_pco /mnt/prooffs
EOF
}

if [ $# -lt 2 ]; then
  usage >&2
  exit 2
fi

SRC=$1
MNT=$2

if [ ! -d "$SRC" ]; then
  echo "Source directory not found: $SRC" >&2
  exit 2
fi

mkdir -p "$MNT"

uname_s=$(uname -s | tr '[:upper:]' '[:lower:]')
if [[ "$uname_s" == linux* ]]; then
  echo "[i] Linux detected — performing bind mount (ro)" >&2
  if ! mountpoint -q "$MNT" 2>/dev/null; then
    sudo mount --bind "$SRC" "$MNT"
  fi
  sudo mount -o remount,ro,bind "$MNT"
  echo "[ok] Mounted $SRC -> $MNT (ro, bind)"
  exit 0
elif [[ "$uname_s" == darwin* ]]; then
  echo "[i] macOS detected — using nullfs (ro)" >&2
  sudo mount -t nullfs -o ro "$SRC" "$MNT"
  echo "[ok] Mounted $SRC -> $MNT (ro, nullfs)"
  exit 0
else
  echo "[!] Unsupported OS: $uname_s" >&2
  echo "Try a FUSE-based driver or perform a manual ro-mount." >&2
  exit 4
fi
