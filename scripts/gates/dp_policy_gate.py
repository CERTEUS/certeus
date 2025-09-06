#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/dp_policy_gate.py                      |
# | ROLE: Run OPA DP policy tests (report-only by default)       |
# | PLIK: scripts/gates/dp_policy_gate.py                      |
# | ROLA: Uruchamia testy OPA DP (domyślnie report-only)         |
# +-------------------------------------------------------------+

"""
PL: Gate polityki ochrony danych (DP/ZK) w OPA/Rego. Próbuje wykonać `opa test`
    na `policies/security/*.rego`. Jeśli brak `opa`, podejmuje próbę przez Docker
    (`openpolicyagent/opa:latest`). Wygenerowany raport:
      - out/dp_policy_report.json (status: ok/failed/skipped, details)
    Egzekwowanie (exit 1) tylko gdy `DP_POLICY_ENFORCE=1`.

EN: Data protection (DP/ZK) OPA/Rego gate. Tries `opa test` on
    `policies/security/*.rego`. Falls back to Docker image if CLI is missing.
    Report is written to `out/dp_policy_report.json`. Enforcement (exit 1)
    only when `DP_POLICY_ENFORCE=1`.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
from typing import Any


def _run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, text=True, capture_output=True, check=False)


def _ensure_out() -> Path:
    p = Path("out")
    p.mkdir(parents=True, exist_ok=True)
    return p


def _opa_test_cli() -> tuple[bool, str, str]:
    if shutil.which("opa"):
        cp = _run(["opa", "test", "policies/security"])
        return (cp.returncode == 0, cp.stdout, cp.stderr)
    return (False, "", "opa cli not found")


def _opa_test_docker() -> tuple[bool, str, str]:
    if not shutil.which("docker"):
        return (False, "", "docker not found")
    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{str(Path.cwd())}:/src",
        "openpolicyagent/opa:latest",
        "test",
        "/src/policies/security",
    ]
    cp = _run(cmd)
    return (cp.returncode == 0, cp.stdout, cp.stderr)


def _eval_samples() -> dict[str, Any]:
    samples: dict[str, Any] = {}
    # Deny: PII present without redaction
    inp1 = {"payload": {"email": "a@b"}, "context": {"redacted": False}}
    # Allow: Redacted
    inp2 = {"payload": {"email": "a@b"}, "context": {"redacted": True}}
    # Allow: No PII
    inp3 = {"payload": {"msg": "ok"}, "context": {"redacted": False}}
    samples["deny_no_redaction"] = inp1
    samples["allow_redacted"] = inp2
    samples["allow_no_pii"] = inp3
    # Try to evaluate with OPA CLI if available
    results: dict[str, Any] = {"samples": samples, "eval": {}}
    if shutil.which("opa"):
        for name, inp in samples.items():
            q = "data.security.dp.allow"
            cp = _run(
                ["opa", "eval", "-I", "-f", "raw", q, "-i=/dev/stdin"],
            )
            # Provide input via stdin (not supported by our simple wrapper), fallback to skip
            # Simpler path: write temp file
            tmp = Path("out") / f"dp_{name}.json"
            tmp.write_text(json.dumps(inp), encoding="utf-8")
            cp = _run(["opa", "eval", "-f", "raw", q, f"-i={str(tmp)}"])
            results["eval"][name] = (cp.stdout or "").strip()
    return results


def main() -> int:
    out = _ensure_out()
    enforce = (os.getenv("DP_POLICY_ENFORCE") or "0").strip().lower() in {"1", "true"}
    ok, so, se = _opa_test_cli()
    used = "cli"
    if not ok and "not found" in se.lower():
        ok, so, se = _opa_test_docker()
        used = "docker"
    status = "ok" if ok else ("skipped" if "not found" in se.lower() else "failed")
    report = {
        "used": used,
        "status": status,
        "stdout": so,
        "stderr": se,
    }
    try:
        report["samples"] = _eval_samples()
    except Exception:
        pass
    (out / "dp_policy_report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    if ok:
        (out / "dp_policy_ok.txt").write_text("ok", encoding="utf-8")
    if enforce and not ok:
        print("DP Policy Gate: FAIL (enforced)")
        return 1
    print(f"DP Policy Gate: {status} (via {used})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
