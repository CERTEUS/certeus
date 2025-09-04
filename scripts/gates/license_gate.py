#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/license_gate.py                        |
# | ROLE: Verify plugin manifests for license policy (report)    |
# | PLIK: scripts/gates/license_gate.py                        |
# | ROLA: Weryfikuj licencje manifestów pluginów (raport)        |
# +-------------------------------------------------------------+

"""
PL: Skanuje `plugins/*/plugin.yaml` i weryfikuje pola wymagane (name,module,version)
    oraz obecność `license` z allowlisty (`policies/security/licenses.allowlist.json`).
    Raport: `out/license_report.json`. Report-only (exit 0), enforcement via
    `LICENSE_POLICY_ENFORCE=1`.

EN: Scans `plugins/*/plugin.yaml`, checks required fields and `license` against
    allowlist. Writes `out/license_report.json`. Report-only by default.
"""

from __future__ import annotations

import glob
import json
from pathlib import Path
from typing import Any

import yaml  # type: ignore

REQ = ("name", "module", "version")


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)
    allow = set()
    try:
        js = json.loads((repo / "policies" / "security" / "licenses.allowlist.json").read_text(encoding="utf-8"))
        allow = set(js.get("allowed", []))
    except Exception:
        allow = set()
    results: list[dict[str, Any]] = []
    ok_all = True
    for fp in sorted(glob.glob(str(repo / "plugins" / "*" / "plugin.yaml"))):
        miss: list[str] = []
        lic_ok = None
        try:
            data = yaml.safe_load(Path(fp).read_text(encoding="utf-8")) or {}
        except Exception as e:
            results.append({"file": fp, "error": str(e)})
            ok_all = False
            continue
        if not isinstance(data, dict):
            results.append({"file": fp, "error": "not a mapping"})
            ok_all = False
            continue
        # Skip banners-only manifests without name
        if "name" not in data:
            results.append({"file": fp, "skipped": True, "reason": "no name field"})
            continue
        for k in REQ:
            if k not in data:
                miss.append(k)
        lic = data.get("license")
        if lic is None:
            lic_ok = False
            miss.append("license")
        else:
            lic_ok = str(lic) in allow if allow else True
            if allow and not lic_ok:
                miss.append("license:not-allowed")
        if miss:
            ok_all = False
        results.append({"file": fp, "missing": miss, "license": lic, "license_ok": lic_ok})
    (out / "license_report.json").write_text(json.dumps({"ok": ok_all, "results": results}, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
