#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/git_push.py                                  |
# | ROLE: Project script.                                       |
# | PLIK: scripts/git_push.py                                  |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+

"""
PL: Pomocnik push do GitHuba z użyciem tokenu z ENV (bez logowania sekretów).
    Wspiera gałąź docelową przez argument `--to` (domyślnie work/daily).

EN: Helper to push to GitHub using a token from ENV (no secret logging).
    Supports target branch via `--to` (default work/daily).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess


def _run(cmd: list[str]) -> None:
    subprocess.run(cmd, check=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--to", default="work/daily", help="Target branch (default: work/daily)")
    args = ap.parse_args()

    # Prefer explicit user/token; support ADMIN_TOKEN fallback
    user = os.getenv("GITHUB_USER") or os.getenv("GH_USER") or os.getenv("GIT_USER") or "x-access-token"
    token = (
        os.getenv("GITHUB_PUSH_TOKEN") or os.getenv("GITHUB_TOKEN") or os.getenv("GH_TOKEN") or os.getenv("ADMIN_TOKEN")
    )
    if not token:
        # Fallback: try GitHub CLI token if available
        try:
            out = subprocess.run(["gh", "auth", "token"], check=True, capture_output=True, text=True)
            cand = (out.stdout or "").strip()
            if cand:
                token = cand
        except Exception:
            pass
    if not token:
        raise SystemExit("Missing push token in env (set ADMIN_TOKEN/GITHUB_PUSH_TOKEN) or login via `gh auth login`")

    # Write credentials to .git-credentials for credential.helper=store
    cred_file = Path(".git-credentials")
    cred_file.write_text(f"https://{user}:{token}@github.com\n", encoding="utf-8")

    # Configure helper locally (do not leak secrets in logs)
    _run(["git", "config", "credential.helper", "store"])

    # Push current HEAD to target branch
    _run(["git", "push", "-u", "origin", f"HEAD:{args.to}"])

    # Optionally cleanup volatile credentials
    if (os.getenv("GITHUB_PUSH_TOKEN_VOLATILE") or "").strip() in {"1", "true", "True"}:
        try:
            cred_file.unlink(missing_ok=True)  # type: ignore[arg-type]
        except Exception:
            pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
