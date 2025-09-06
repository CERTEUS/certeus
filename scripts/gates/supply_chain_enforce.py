#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/supply_chain_enforce.py                |
# | ROLE: Supply-chain enforcement (optional)                   |
# | PLIK: scripts/gates/supply_chain_enforce.py                |
# | ROLA: Egzekwowanie supply-chain (opcjonalne)                |
# +-------------------------------------------------------------+

"""
PL: Egzekwowanie minimalnych warunków supply-chain:
    - obecność SBOM (`sbom.json`) lub artefaktu `artifact.json`/attestacji.
    - gdy SUPPLY_CHAIN_ENFORCE=1 brak => exit 1, w przeciwnym wypadku INFO.

EN: Enforce minimal supply-chain conditions:
    - presence of SBOM (`sbom.json`) or `artifact.json`/attestation.
    - when SUPPLY_CHAIN_ENFORCE=1 missing => exit 1, otherwise INFO.
    - additionally enforce plugins when enabled (deny by default without SBOM/Provenance).
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


def _bool_env(name: str) -> bool:
    return (os.getenv(name) or "").strip().lower() in {"1", "true", "on", "yes"}


def main() -> int:
    # Use current working directory as repository root to support sandboxed CI and tests
    repo = Path(".").resolve()
    out = repo / "out"
    out.mkdir(parents=True, exist_ok=True)

    enforce = _bool_env("SUPPLY_CHAIN_ENFORCE")
    require_cosign = _bool_env("REQUIRE_COSIGN")

    # Repo-level artifacts
    repo_ok = (repo / "sbom.json").exists() or (repo / "artifact.json").exists()

    vio: list[str] = []
    warn: list[str] = []
    # Plugin-level checks (reuse report-only gate logic)
    try:
        from scripts.gates.plugin_supply_chain_gate import check as plugin_check  # type: ignore

        pv, pw = plugin_check(repo)
        vio.extend(pv)
        warn.extend(pw)
    except Exception:
        warn.append("plugin gate not available; skipping plugin checks")

    # If cosign is required, treat lack of signatures as violation
    if require_cosign:
        plugins = repo / "plugins"
        if plugins.exists():
            for d in plugins.iterdir():
                if not d.is_dir() or not (d / "plugin.yaml").exists():
                    continue
                sc_dir = d / "supply_chain"
                has_sig = (
                    list(d.glob("*.sig"))
                    or list(d.glob("*.cert"))
                    or list(sc_dir.glob("*.sig"))
                    or list(sc_dir.glob("*.cert"))
                )
                if not has_sig:
                    vio.append(f"{d.name}: missing cosign signatures (REQUIRED)")

    report: dict[str, Any] = {
        "repo_ok": bool(repo_ok),
        "violations": vio,
        "warnings": warn,
        "enforce": bool(enforce),
        "require_cosign": bool(require_cosign),
    }
    (out / "supply_chain_enforce.json").write_text(json.dumps(report, indent=2), encoding="utf-8")

    if not repo_ok and enforce:
        print("supply-chain: FAIL (missing sbom.json/artifact.json)")
        return 1
    if vio and enforce:
        print("supply-chain: FAIL (plugins: violations present)")
        for v in vio:
            print(" -", v)
        return 1

    # Non-enforcing summary
    if not repo_ok:
        print("supply-chain: INFO (no repo sbom/artifact)")
    if warn:
        print("supply-chain: WARN (plugins)")
        for w in warn:
            print(" -", w)
    print("supply-chain: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
