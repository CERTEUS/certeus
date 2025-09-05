#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/pack_abi_semver_gate.py               |
# | ROLE: Project gate script.                                   |
# | PLIK: scripts/gates/pack_abi_semver_gate.py               |
# | ROLA: Skrypt bramki projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Bramka ABI/SemVer dla Domain Packs (plugins/*/plugin.yaml).
    - Weryfikuje poprawność semver.
    - Buduje deskryptor ABI (moduł, kształt register/Plugin.register).
    - Jeśli istnieje `plugins/<name>/abi_baseline.json`, porównuje deskryptory i
      wymaga podbicia MAJOR w przypadku zmiany ABI.

EN: ABI/SemVer gate for Domain Packs (plugins/*/plugin.yaml).
    - Validates semver string.
    - Builds ABI descriptor (module path, shape of register/Plugin.register).
    - If `plugins/<name>/abi_baseline.json` exists, compares descriptors and
      requires MAJOR bump when ABI changed.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from dataclasses import asdict, dataclass, fields
import importlib
import inspect
from inspect import Parameter as _P
import json
import os
from pathlib import Path
import sys
from typing import Any

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover
    yaml = None  # type: ignore

# === MODELE / MODELS ===


@dataclass(slots=True)
class AbiDescriptor:
    module: str
    has_module_register: bool
    module_register_arity: int | None
    has_class_plugin: bool
    has_class_register: bool
    class_register_arity: int | None


# === LOGIKA / LOGIC ===


def _load_manifest(p: Path) -> dict[str, Any]:
    if yaml is not None:
        try:
            data = yaml.safe_load(p.read_text(encoding="utf-8"))
            return data or {}
        except Exception:
            return {}
    # Fallback: naive K: V parser
    out: dict[str, Any] = {}
    for raw in p.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or ":" not in line:
            continue
        k, v = line.split(":", 1)
        out[k.strip()] = v.strip().strip("'\"")
    return out


def _semver_parts(s: str) -> tuple[int, int, int] | None:
    try:
        major, minor, patch = s.split(".")
        return int(major), int(minor), int(patch)
    except Exception:
        return None


def _abi_for_module(mod_path: str) -> AbiDescriptor:
    has_mod_reg = False
    mod_reg_arity: int | None = None
    has_cls = False
    has_cls_reg = False
    cls_reg_arity: int | None = None
    try:
        # Reload module if already imported (ensure fresh source)
        if mod_path in sys.modules:
            del sys.modules[mod_path]
        mod = importlib.import_module(mod_path)
    except Exception:
        return AbiDescriptor(
            module=mod_path,
            has_module_register=False,
            module_register_arity=None,
            has_class_plugin=False,
            has_class_register=False,
            class_register_arity=None,
        )
    reg = getattr(mod, "register", None)
    if callable(reg):
        has_mod_reg = True
        try:
            sig = inspect.signature(reg)
            allowed = (_P.POSITIONAL_ONLY, _P.POSITIONAL_OR_KEYWORD)
            mod_reg_arity = len([p for p in sig.parameters.values() if p.kind in allowed])
        except Exception:
            mod_reg_arity = None
    Plugin = getattr(mod, "Plugin", None)
    if Plugin is not None:
        has_cls = True
        inst = None
        try:
            inst = Plugin()
        except Exception:
            inst = None
        reg_m = getattr(Plugin if inst is None else inst, "register", None)
        if callable(reg_m):
            has_cls_reg = True
            try:
                sig = inspect.signature(reg_m)
                allowed = (_P.POSITIONAL_ONLY, _P.POSITIONAL_OR_KEYWORD)
                cls_reg_arity = len([p for p in sig.parameters.values() if p.kind in allowed])
            except Exception:
                cls_reg_arity = None
    return AbiDescriptor(
        module=mod_path,
        has_module_register=has_mod_reg,
        module_register_arity=mod_reg_arity,
        has_class_plugin=has_cls,
        has_class_register=has_cls_reg,
        class_register_arity=cls_reg_arity,
    )


def _descriptor_changed(prev: AbiDescriptor, cur: AbiDescriptor) -> bool:
    return asdict(prev) != asdict(cur)


def check(repo_root: str | Path | None = None) -> tuple[list[str], list[str]]:
    root = Path(repo_root or ".").resolve()
    violations: list[str] = []
    warnings: list[str] = []
    plugdir = root / "plugins"
    if not plugdir.exists():
        return violations, warnings
    for man in plugdir.glob("*/plugin.yaml"):
        data = _load_manifest(man)
        name = str(data.get("name") or man.parent.name)
        mod = str(data.get("module") or "").strip()
        ver = str(data.get("version") or data.get("ver") or "").strip()
        parts = _semver_parts(ver)
        ctx = f"{name} ({man})"
        if not parts:
            violations.append(f"{ctx}: invalid semver '{ver or '<empty>'}'")
            continue
        desc = _abi_for_module(mod) if mod else AbiDescriptor(mod, False, None, False, False, None)

        baseline_p = man.parent / "abi_baseline.json"
        if baseline_p.exists():
            try:
                raw = json.loads(baseline_p.read_text(encoding="utf-8"))
                # Tolerate extra keys (e.g., __version__) by projecting onto known fields
                allowed = {f.name for f in fields(AbiDescriptor)}
                prev_dict = {k: v for k, v in (raw or {}).items() if k in allowed}
                prev = AbiDescriptor(**prev_dict)
                if (os.getenv("DEBUG_PACK_ABI") or "").strip() in {"1", "true", "True"}:
                    print("[DEBUG] prev desc:", asdict(prev))
                if (os.getenv("DEBUG_PACK_ABI") or "").strip() in {"1", "true", "True"}:
                    print("[DEBUG] cur  desc:", asdict(desc))
                if _descriptor_changed(prev, desc):
                    # ABI changed — require major bump
                    major_cur = parts[0]
                    # try to read previous version (optional 'version' in baseline file)
                    prev_ver = raw.get("__version__")
                    prev_parts = _semver_parts(prev_ver) if isinstance(prev_ver, str) else None
                    # If previous version unknown, be conservative and require major bump
                    if (prev_parts is None) or (major_cur <= prev_parts[0]):
                        violations.append(
                            f"{ctx}: ABI changed but major version not bumped (prev={prev_ver}, cur={ver})"
                        )
                    else:
                        warnings.append(f"{ctx}: ABI changed; ensure major bump is intentional (prev baseline differs)")
            except Exception:
                warnings.append(f"{ctx}: cannot parse abi_baseline.json; skipping ABI compare")
        else:
            # No baseline — report-only; suggest creating one
            warnings.append(f"{ctx}: no abi_baseline.json; run update_abi_baselines.py to create baseline")
    return violations, warnings


def main() -> int:
    vio, warn = check()
    if warn:
        print("Pack ABI/SemVer: WARNINGS")
        for w in warn:
            print(" -", w)
    if vio:
        print("Pack ABI/SemVer: VIOLATIONS")
        for v in vio:
            print(" -", v)
    enforce = (os.getenv("ENFORCE_PACK_ABI_SEMVER") or "").strip() in {"1", "true", "True"}
    if vio and enforce:
        return 1
    print(
        f"Pack ABI/SemVer: {'OK (report-only)' if not enforce else ('FAIL' if vio else 'OK')} — "
        f"{len(vio)} violations, {len(warn)} warnings"
    )
    return 0


# === I/O / ENDPOINTS ===

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === TESTY / TESTS ===
