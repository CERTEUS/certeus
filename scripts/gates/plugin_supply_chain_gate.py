#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/plugin_supply_chain_gate.py            |
# | ROLE: Project gate script.                                 |
# | PLIK: scripts/gates/plugin_supply_chain_gate.py            |
# | ROLA: Skrypt bramki projektu.                              |
# +-------------------------------------------------------------+

"""
PL: Bramka supply‑chain dla wtyczek (report‑only domyślnie).
    Dla każdego `plugins/*/plugin.yaml` sprawdza obecność artefaktów:
    - SBOM (np. `sbom.json`, `sbom.cdx.json` lub `supply_chain/sbom*.json`),
    - Provenance (np. `provenance.json` lub `supply_chain/provenance*.json`),
    - (opcjonalnie) podpisów cosign (`*.sig`, `*.cert`).

EN: Plugin supply‑chain gate (report‑only by default).
    For each `plugins/*/plugin.yaml`, checks presence of artifacts:
    - SBOM (e.g., `sbom.json`, `sbom.cdx.json`, or `supply_chain/sbom*.json`),
    - Provenance (e.g., `provenance.json` or `supply_chain/provenance*.json`),
    - (optional) cosign signatures (`*.sig`, `*.cert`).
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from collections.abc import Iterable
import os
from pathlib import Path
from typing import Any

try:  # optional YAML parser; fallback to naive
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

# === KONFIGURACJA / CONFIGURATION ===

SBOM_NAMES = ("sbom.json", "sbom.cdx.json")
PROV_NAMES = ("provenance.json",)
SIG_SUFFIXES = (".sig", ".cert")

# === LOGIKA / LOGIC ===


def _naive_yaml(path: Path) -> dict[str, Any]:
    data: dict[str, Any] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or ":" not in line:
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


def _iter_plugin_dirs(root: Path) -> Iterable[Path]:
    plugins = root / "plugins"
    if not plugins.exists():
        return []
    for d in plugins.iterdir():
        if d.is_dir() and (d / "plugin.yaml").exists():
            yield d


def _glob_any(base: Path, patterns: list[str]) -> bool:
    for pat in patterns:
        if list(base.glob(pat)):
            return True
    return False


def check(root: str | Path | None = None) -> tuple[list[str], list[str]]:
    """PL/EN: Returns (violations, warnings)."""
    repo = Path(root or ".").resolve()
    vio: list[str] = []
    warn: list[str] = []
    for d in _iter_plugin_dirs(repo):
        man = _load_manifest(d / "plugin.yaml")
        name = str(man.get("name") or d.name)

        # SBOM candidates
        has_sbom = any((d / n).exists() for n in SBOM_NAMES) or _glob_any(
            d / "supply_chain", ["sbom*.json"]
        )
        # Provenance candidates
        has_prov = any((d / n).exists() for n in PROV_NAMES) or _glob_any(
            d / "supply_chain", ["provenance*.json"]
        )
        # Cosign hints (optional)
        has_sig = _glob_any(d, [f"*{suf}" for suf in SIG_SUFFIXES]) or _glob_any(
            d / "supply_chain", [f"*{suf}" for suf in SIG_SUFFIXES]
        )

        if not has_sbom:
            vio.append(
                f"{name}: missing SBOM (sbom.json / sbom.cdx.json / supply_chain/sbom*.json)"
            )
        if not has_prov:
            vio.append(
                f"{name}: missing provenance (provenance.json / supply_chain/provenance*.json)"
            )
        if not has_sig:
            warn.append(f"{name}: cosign signatures not found (optional: *.sig/*.cert)")

    return vio, warn


def main() -> int:
    vio, warn = check()
    if warn:
        print("Plugin Supply-Chain: WARNINGS")
        for w in warn:
            print(" -", w)
    if vio:
        print("Plugin Supply-Chain: VIOLATIONS")
        for v in vio:
            print(" -", v)
    enforce = (os.getenv("ENFORCE_PLUGIN_SUPPLY") or "").strip() in {
        "1",
        "true",
        "True",
    }
    if vio and enforce:
        return 1
    print(
        f"Plugin Supply-Chain: {'OK (report-only)' if not enforce else ('FAIL' if vio else 'OK')} — "
        f"{len(vio)} violations, {len(warn)} warnings"
    )
    return 0


# === I/O / ENDPOINTS ===

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === TESTY / TESTS ===
