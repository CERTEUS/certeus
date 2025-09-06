#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_pack_abi_semver_gate.py            |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_pack_abi_semver_gate.py            |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+

"""
PL: Testy kontraktowe bramki ABI/SemVer dla Domain Packs.

EN: Contract tests for ABI/SemVer gate for Domain Packs.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path

from scripts.gates.pack_abi_semver_gate import check
from scripts.packs.update_abi_baselines import main as update_baselines


def _write(p: Path, content: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")


def test_pack_abi_semver_gate_detects_abi_change_requires_major(
    tmp_path: Path, monkeypatch
) -> None:
    # Prepare a temporary plugin structure
    repo = tmp_path
    plug = repo / "plugins" / "my_pack"
    # Python package for module path
    _write(repo / "tmp_pkg" / "__init__.py", "")
    _write(repo / "tmp_pkg" / "my_pack" / "__init__.py", "")
    # Baseline module with register(api)
    _write(
        repo / "tmp_pkg" / "my_pack" / "main.py",
        """
from __future__ import annotations

def register(api):
    return None
""",
    )
    # Manifest v1.0.0
    _write(
        plug / "plugin.yaml",
        """
name: my_pack
version: 1.0.0
module: tmp_pkg.my_pack.main
register: register
""".strip()
        + "\n",
    )

    # Ensure imports can locate our temp package
    monkeypatch.syspath_prepend(str(repo))
    # Initially: no baseline -> warning only
    vio, warn = check(repo_root=repo)
    assert not vio
    assert any("no abi_baseline.json" in w for w in warn)

    # Create baseline
    monkeypatch.chdir(repo)
    rc = update_baselines()
    assert rc == 0
    assert (plug / "abi_baseline.json").exists()

    # Change ABI (register signature) without major bump -> violation
    _write(
        repo / "tmp_pkg" / "my_pack" / "main.py",
        """
from __future__ import annotations

def register(api, name):
    return None
""",
    )
    _write(
        plug / "plugin.yaml",
        """
name: my_pack
version: 1.1.0
module: tmp_pkg.my_pack.main
register: register
""".strip()
        + "\n",
    )
    vio, warn = check(repo_root=repo)
    assert any("ABI changed" in v for v in vio), vio

    # Major bump allows change -> no violations (maybe warning)
    _write(
        plug / "plugin.yaml",
        """
name: my_pack
version: 2.0.0
module: tmp_pkg.my_pack.main
register: register
""".strip()
        + "\n",
    )
    vio, warn = check(repo_root=repo)
    assert not vio
    # Should warn about ABI changed but acceptable with major bump
    assert warn
