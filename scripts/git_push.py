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
import json
import os
from pathlib import Path
import subprocess
import urllib.request


def _run(cmd: list[str]) -> None:
    subprocess.run(cmd, check=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--to", default="work/daily", help="Target branch (default: work/daily)")
    args = ap.parse_args()

    # Prefer explicit user/token; support ADMIN_TOKEN fallback

    user = os.getenv("GITHUB_USER") or os.getenv("GH_USER") or os.getenv("GIT_USER")
    # Consider USER as last resort (avoid common container users)
    if not user:
        u = os.getenv("USER")
        if u and u not in {"root", "vscode", "codespace", "code"}:
            user = u
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
        # Fallback: read token from local files (ignored by Git)
        for name in (".devkeys/admin_token.txt", ".devkeys/github_pat.txt", ".devkeys/token.txt"):
            p = Path(name)
            if p.exists():
                token = p.read_text(encoding="utf-8").strip()
                if token:
                    break
    if not token:
        raise SystemExit("Missing push token: set ADMIN_TOKEN/GITHUB_PUSH_TOKEN or provide .devkeys/admin_token.txt")

    # Resolve repo owner/name from origin
    _proc = subprocess.run(["git", "remote", "get-url", "origin"], check=True, capture_output=True, text=True)
    origin = (_proc.stdout or "").strip()
    # Accept https://github.com/owner/repo(.git)
    owner = "CERTEUS"
    repo = "certeus"
    try:
        if origin.startswith("http"):
            parts = origin.rstrip("/").split("/")
            owner = parts[-2]
            repo = parts[-1]
            if repo.endswith(".git"):
                repo = repo[:-4]
    except Exception:
        pass

    # Determine username if not provided
    if not user:
        # 1) local file (.devkeys/github_user.txt)
        p = Path(".devkeys/github_user.txt")
        if p.exists():
            try:
                user = p.read_text(encoding="utf-8").strip()
            except Exception:
                user = None
    if not user:
        # 2) query GitHub API to get login owner of token
        try:
            req = urllib.request.Request("https://api.github.com/user", headers={"Authorization": f"token {token}"})
            with urllib.request.urlopen(req, timeout=5) as resp:  # nosec B310
                you = json.loads(resp.read().decode("utf-8"))
                cand = you.get("login")
                if isinstance(cand, str) and cand:
                    user = cand
        except Exception:
            user = None
    if not user:
        # 3) fallback
        user = "x-access-token"

    # Optional: verify token has push permission
    try:
        req = urllib.request.Request(
            f"https://api.github.com/repos/{owner}/{repo}", headers={"Authorization": f"token {token}"}
        )
        with urllib.request.urlopen(req, timeout=5) as resp:  # nosec B310
            meta = json.loads(resp.read().decode("utf-8"))
            perms = meta.get("permissions") or {}
            if not perms.get("push", False):
                print("warning: token may lack push permission for repo; proceeding anyway")
    except Exception:
        pass

    # Write credentials to ~/.git-credentials for credential.helper=store
    home = os.path.expanduser("~") or "/root"
    cred_file = Path(home) / ".git-credentials"
    cred_file.parent.mkdir(parents=True, exist_ok=True)
    # Append idempotently host-level and repo-level entries
    host_line = f"https://{user}:{token}@github.com\n"
    repo_line = None
    try:
        _proc2 = subprocess.run(["git", "remote", "get-url", "origin"], check=True, capture_output=True, text=True)
        origin2 = (_proc2.stdout or "").strip()
        if origin2.startswith("http"):
            repo_line = f"https://{user}:{token}@{origin2.split('://', 1)[1]}\n"
    except Exception:
        pass
    cur = ""
    if cred_file.exists():
        try:
            cur = cred_file.read_text(encoding="utf-8")
        except Exception:
            cur = ""
    new_content = cur
    if host_line not in cur:
        new_content += host_line
    if repo_line and repo_line not in cur:
        new_content += repo_line
    cred_file.write_text(new_content, encoding="utf-8")

    # Configure helper globally (do not leak secrets in logs)
    _run(["git", "config", "--global", "credential.helper", "store"])
    _run(["git", "config", "--global", "credential.useHttpPath", "true"])

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
