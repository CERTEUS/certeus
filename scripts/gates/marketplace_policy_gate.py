#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/marketplace_policy_gate.py             |
# | ROLE: Project gate script.                                   |
# | PLIK: scripts/gates/marketplace_policy_gate.py             |
# | ROLA: Skrypt bramki projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Bramka polityk Marketplace (report‑only domyślnie).
    Sprawdza manifesty pluginów (`plugins/*/plugin.yaml`) pod kątem:
    - poprawnego semver w `version`,
    - dozwolonej licencji (jeśli obecna),
    - obecności metadanych podpisu (jeśli obecne: podstawowa walidacja).

EN: Marketplace policy gate (report‑only by default).
    Validates plugin manifests (`plugins/*/plugin.yaml`) for:
    - valid semver in `version`,
    - allowed license (if present),
    - signature metadata presence (if present: basic sanity check).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Iterable
import os
from pathlib import Path
import re
from typing import Any

try:  # optional YAML parser; fallback to naive parser
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

# === KONFIGURACJA / CONFIGURATION ===

ALLOWED_LICENSES: set[str] = {
    "MIT",
    "Apache-2.0",
    "BSD-2-Clause",
    "BSD-3-Clause",
}

# SemVer: MAJOR.MINOR.PATCH(-prerelease)?(+build)?
SEMVER_RE = re.compile(
    r"^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)(?:-([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?(?:\+([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?$"
)

# === LOGIKA / LOGIC ===


def _naive_yaml(path: Path) -> dict[str, Any]:
    data: dict[str, Any] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if ":" not in line:
            continue
        k, v = line.split(":", 1)
        key = k.strip()
        val = v.strip().strip("\"'")
        if key:
            data[key] = val
    return data


def _load_manifest(p: Path) -> dict[str, Any]:
    if yaml is not None:
        try:
            return yaml.safe_load(p.read_text(encoding="utf-8")) or {}
        except Exception:
            return {}
    return _naive_yaml(p)


def _iter_plugin_manifests(root: Path) -> Iterable[Path]:
    plugdir = root / "plugins"
    if not plugdir.exists():
        return []
    for sub in plugdir.iterdir():
        if sub.is_dir():
            man = sub / "plugin.yaml"
            if man.exists():
                yield man


def check(repo_root: str | Path | None = None) -> tuple[list[str], list[str]]:
    """PL/EN: Zwraca (violations, warnings) bez rzucania wyjątków."""
    root = Path(repo_root or ".").resolve()
    violations: list[str] = []
    warnings: list[str] = []
    # Optional: read packs overlay state to correlate signature presence (advisory)
    state_path = root / "data" / "packs_state.json"
    try:
        state = {}
        if state_path.exists():
            import json as _json

            state = _json.loads(state_path.read_text(encoding="utf-8")) or {}
            if not isinstance(state, dict):
                state = {}
    except Exception:
        state = {}

    for man in _iter_plugin_manifests(root):
        m = _load_manifest(man)
        name = str(m.get("name") or "").strip()
        ver = str(m.get("version") or "").strip()
        lic = (m.get("license") or m.get("licence") or "").strip()
        sig = (m.get("signature") or "").strip()

        ctx = f"{man.parent.name} ({man})"

        if not name:
            violations.append(f"{ctx}: missing name")
        if not ver or not SEMVER_RE.match(ver):
            violations.append(f"{ctx}: invalid or missing semver version '{ver or '<empty>'}'")

        if lic:
            if lic not in ALLOWED_LICENSES:
                violations.append(f"{ctx}: disallowed license '{lic}' (allow: {sorted(ALLOWED_LICENSES)})")
        else:
            warnings.append(f"{ctx}: license not specified (advised: one of {sorted(ALLOWED_LICENSES)})")

        if sig:
            # basic sanity: at least 40 hex/base64‑ish chars
            if len(sig) < 40:
                warnings.append(f"{ctx}: signature present but looks too short")
        else:
            warnings.append(f"{ctx}: signature not present (recommended)")

        # If pack is enabled/installed in state and no signature recorded, add advisory
        try:
            entry = state.get(name) if isinstance(state, dict) else None
            if isinstance(entry, dict):
                enabled = bool(entry.get("enabled", False))
                has_sig = bool(entry.get("signature"))
                if enabled and not has_sig:
                    warnings.append(f"{ctx}: enabled without installed signature (state overlay)")
                # Version mismatch advisory (installed vs manifest)
                inst_ver = str(entry.get("installed_version") or "").strip()
                if inst_ver and ver and inst_ver != ver:
                    warnings.append(f"{ctx}: installed_version '{inst_ver}' differs from manifest version '{ver}'")
        except Exception:
            pass

    return violations, warnings


def main() -> int:
    vio, warn = check()
    enforce = (os.getenv("ENFORCE_MARKETPLACE_POLICY") or "").strip() in {
        "1",
        "true",
        "True",
    }
    if warn:
        print("Marketplace Policy: WARNINGS")
        for w in warn:
            print(" -", w)
    if vio:
        print("Marketplace Policy: VIOLATIONS")
        for v in vio:
            print(" -", v)
    if vio and enforce:
        return 1
    print(
        f"Marketplace Policy: {'OK (report-only)' if not enforce else ('FAIL' if vio else 'OK')} — "
        f"{len(vio)} violations, {len(warn)} warnings"
    )
    return 0


# === I/O / ENDPOINTS ===

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === TESTY / TESTS ===
