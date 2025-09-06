#!/usr/bin/env bash
set -euo pipefail
echo "[+] macOS ProofFS mount smoke"
python -m pip install -q fusepy || true
ROOT="data/proof_fs/_smoke"
MP="/tmp/certeus_pfs_mount"
mkdir -p "$ROOT" "$MP"
echo hello > "$ROOT/hello.txt"
python scripts/pfs/fuse_mount.py "$MP" --root "data/proof_fs" --foreground &
PID=$!
sleep 1
ls "$MP/_smoke" | grep -q hello
kill $PID || true
umount "$MP" || true
echo "[OK] macOS mount smoke passed"

