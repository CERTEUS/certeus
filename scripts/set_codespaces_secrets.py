#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/set_codespaces_secrets.py                     |
# | ROLE: Configure Codespaces User Secrets via GitHub API      |
# +-------------------------------------------------------------+

from __future__ import annotations

import argparse
import base64
import json
import os
from pathlib import Path
import urllib.error
import urllib.request


def _env_or_file(*names: str) -> str | None:
    for n in names:
        v = os.getenv(n)
        if v:
            return v
    # fallbacks in .devkeys
    for p in (
        ".devkeys/admin_token.txt",
        ".devkeys/github_pat.txt",
        ".devkeys/token.txt",
    ):
        fp = Path(p)
        if fp.exists():
            try:
                t = fp.read_text(encoding="utf-8").strip()
                if t:
                    return t
            except Exception:
                pass
    return None


def _api(token: str, method: str, url: str, data: dict | None = None) -> dict:
    req = urllib.request.Request(url)
    req.get_method = lambda: method  # type: ignore[assignment]
    req.add_header("Authorization", f"token {token}")
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    body = None
    if data is not None:
        body = json.dumps(data).encode("utf-8")
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, data=body, timeout=15) as resp:  # nosec B310
            raw = resp.read()
            if not raw:
                return {}
            return json.loads(raw.decode("utf-8"))
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8", errors="ignore")
        raise SystemExit(f"API {method} {url} failed: {e.code} {e.reason} -> {msg}") from e


def _ensure_pynacl():
    try:
        import nacl  # noqa: F401
    except Exception:
        import subprocess
        import sys as _sys

        subprocess.run([_sys.executable, "-m", "pip", "install", "PyNaCl"], check=True)


def _encrypt(key_b64: str, value: str) -> str:
    from nacl import encoding, public

    pk = public.PublicKey(base64.b64decode(key_b64), encoder=encoding.RawEncoder)
    sealed = public.SealedBox(pk).encrypt(value.encode("utf-8"))
    return base64.b64encode(sealed).decode("utf-8")


def main() -> int:
    ap = argparse.ArgumentParser(description="Set Codespaces User Secrets for this account (and grant repo access)")
    ap.add_argument(
        "--repo",
        default="CERTEUS/certeus",
        help="owner/repo to grant access to secrets",
    )
    ap.add_argument(
        "--set",
        nargs="*",
        default=["ADMIN_TOKEN", "GITHUB_USER"],
        help="Secret names to set",
    )
    args = ap.parse_args()

    token = _env_or_file("ADMIN_TOKEN", "GITHUB_PUSH_TOKEN", "GITHUB_TOKEN", "GH_TOKEN")
    if not token:
        raise SystemExit("Missing admin token in env or .devkeys/admin_token.txt")

    # Values to set
    val_map: dict[str, str] = {}
    # ADMIN_TOKEN value equals the same token by default
    if "ADMIN_TOKEN" in args.__dict__.get("set", []):
        val_map["ADMIN_TOKEN"] = token
    # GITHUB_USER from env or file
    gh_user = _env_or_file("GITHUB_USER", "GH_USER", "GIT_USER")
    if not gh_user:
        p = Path(".devkeys/github_user.txt")
        if p.exists():
            try:
                gh_user = p.read_text(encoding="utf-8").strip()
            except Exception:
                gh_user = None
    if gh_user:
        val_map["GITHUB_USER"] = gh_user

    if not val_map:
        print("Nothing to set.")
        return 0

    # Repo id to grant
    owner, repo = args.repo.split("/", 1)
    repo_meta = _api(token, "GET", f"https://api.github.com/repos/{owner}/{repo}")
    repo_id = repo_meta.get("id")
    if not isinstance(repo_id, int):
        raise SystemExit("Could not resolve repository id")

    # Public key for user codespaces secrets
    pub = _api(token, "GET", "https://api.github.com/user/codespaces/secrets/public-key")
    key_id = pub.get("key_id")
    key_b64 = pub.get("key")
    if not (isinstance(key_id, str) and isinstance(key_b64, str)):
        raise SystemExit("Could not obtain Codespaces user public key (check token scopes)")

    _ensure_pynacl()

    # Create/update secrets
    for name, val in val_map.items():
        enc = _encrypt(key_b64, val)
        _api(
            token,
            "PUT",
            f"https://api.github.com/user/codespaces/secrets/{name}",
            {"encrypted_value": enc, "key_id": key_id},
        )
        # Grant repo access
        _api(
            token,
            "PUT",
            f"https://api.github.com/user/codespaces/secrets/{name}/repositories/{repo_id}",
            None,
        )
        print(f"OK: set Codespaces secret '{name}' and granted access to {owner}/{repo}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
