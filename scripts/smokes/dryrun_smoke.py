#!/usr/bin/env python3
"""
PL: Smoke dla /v1/marketplace/dry_run — scenariusze pozytywne/negatywne.
EN: Smoke for /v1/marketplace/dry_run — positive/negative scenarios.
"""

from __future__ import annotations

import json
from pathlib import Path

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _req(name: str, module: str, version: str, sig: str = "sig") -> dict:
    man = f"name: {name}\nmodule: {module}\nversion: '{version}'\n"
    return {"name": name, "manifest_yaml": man, "signature_b64u": sig}


def main() -> int:
    out = {}
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    with TestClient(app) as c:
        out["bad_name"] = c.post("/v1/marketplace/dry_run", json=_req("../evil", "plugins.x.src.main", "1.0.0")).json()
        out["missing_module"] = c.post(
            "/v1/marketplace/dry_run",
            json={"name": "safe", "manifest_yaml": "name: safe\nversion: '1.0.0'\n", "signature_b64u": "sig"},
        ).json()
        out["bad_semver"] = c.post("/v1/marketplace/dry_run", json=_req("safe", "plugins.x.src.main", "abc")).json()
        out["ok_semver"] = c.post("/v1/marketplace/dry_run", json=_req("safe", "plugins.x.src.main", "1.2.3")).json()
    (reports / "smoke_dryrun.json").write_text(json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    print("smoke_dryrun -> reports/smoke_dryrun.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
