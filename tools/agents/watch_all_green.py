#!/usr/bin/env python3
from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
import os
from pathlib import Path
import sys
import time
from typing import Any
from urllib.error import HTTPError
from urllib.request import Request, urlopen


def _now_iso() -> str:
    return datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def _token(repo_root: Path) -> str | None:
    t = os.getenv("GITHUB_TOKEN")
    if t:
        return t.strip()
    p = repo_root / ".control" / "secrets" / "GITHUB_TOKEN.txt"
    try:
        if p.exists():
            return p.read_text(encoding="utf-8").strip()
    except Exception:
        return None
    return None


def _api(url: str, token: str) -> Any:
    req = Request(url)
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("Authorization", f"token {token}")
    with urlopen(req, timeout=30) as r:
        data = r.read()
        return json.loads(data.decode("utf-8"))


def _get_open_prs(owner: str, repo: str, token: str) -> list[dict[str, Any]]:
    url = f"https://api.github.com/repos/{owner}/{repo}/pulls?state=open&per_page=100"
    return list(_api(url, token) or [])


def _check_runs(owner: str, repo: str, sha: str, token: str) -> list[dict[str, Any]]:
    url = f"https://api.github.com/repos/{owner}/{repo}/commits/{sha}/check-runs"
    obj = _api(url, token) or {}
    runs = obj.get("check_runs")
    return list(runs or [])


def _all_success(runs: list[dict[str, Any]]) -> bool:
    if not runs:
        return False
    for r in runs:
        if r.get("status") != "completed":
            return False
        if r.get("conclusion") != "success":
            return False
    return True


def _post_comment(owner: str, repo: str, pr: int, token: str, text: str) -> None:
    url = f"https://api.github.com/repos/{owner}/{repo}/issues/{pr}/comments"
    body = json.dumps({"body": text}).encode("utf-8")
    req = Request(url, data=body, method="POST")
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("Authorization", f"token {token}")
    req.add_header("Content-Type", "application/json")
    with urlopen(req, timeout=30) as r:
        _ = r.read()


def main() -> int:
    ap = argparse.ArgumentParser(description="Watch all PRs in a repo until checks are green.")
    ap.add_argument("--owner", default="CERTEUS")
    ap.add_argument("--repo", default="certeus")
    ap.add_argument("--interval", type=int, default=30)
    ap.add_argument("--comment", type=int, default=0, help="Post success comment to each PR (0/1)")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    out_dir = repo_root / ".control" / ".tmp" / "agents"
    out_dir.mkdir(parents=True, exist_ok=True)
    status_path = out_dir / "watch.status.json"
    green_flag = repo_root / ".control" / ".tmp" / "ALL_GREEN"

    token = _token(repo_root)
    if not token:
        print("[watch] Missing GITHUB_TOKEN; aborting", file=sys.stderr)
        return 2

    print(f"[watch] Watching {args.owner}/{args.repo} every {args.interval}s…")

    while True:
        try:
            prs = _get_open_prs(args.owner, args.repo, token)
            summary = {"ts": _now_iso(), "open_prs": len(prs), "prs": []}
            all_ok = True if prs else False
            for pr in prs:
                num = int(pr.get("number"))
                sha = str(pr.get("head", {}).get("sha") or "")
                runs = _check_runs(args.owner, args.repo, sha, token)
                ok = _all_success(runs)
                summary["prs"].append({"number": num, "sha": sha, "runs": len(runs), "green": ok})
                if not ok:
                    all_ok = False
            status_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
            if all_ok and prs:
                green_flag.write_text(_now_iso(), encoding="utf-8")
                print("[watch] All open PR checks are green.")
                if args.comment:
                    for pr in prs:
                        num = int(pr.get("number"))
                        try:
                            _post_comment(
                                args.owner,
                                args.repo,
                                num,
                                token,
                                "✅ All required checks are green. Proceeding to next steps.",
                            )
                        except HTTPError as e:  # best-effort
                            print(f"[watch] comment failed on PR #{num}: {e}")
                return 0
        except HTTPError as e:
            print(f"[watch] HTTP error: {e}", file=sys.stderr)
        except Exception as e:
            print(f"[watch] error: {e}", file=sys.stderr)
        time.sleep(max(5, int(args.interval)))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
