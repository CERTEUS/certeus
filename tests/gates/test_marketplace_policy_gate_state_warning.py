#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_marketplace_policy_gate_state_warning.py |
# | ROLE: Test module.                                          |
# | PLIK: tests/gates/test_marketplace_policy_gate_state_warning.py |
# | ROLA: Moduł testów.                                         |
# +-------------------------------------------------------------+
"""
PL: Test bramki Marketplace Policy: ostrzeżenie dla enabled bez signature w state.
EN: Marketplace Policy gate: warns when pack is enabled without signature in state overlay.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path

from scripts.gates.marketplace_policy_gate import check


def _w(p: Path, content: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")


def test_warns_enabled_without_signature(tmp_path: Path) -> None:
    repo = tmp_path
    # Minimal plugin
    _w(
        repo / "plugins" / "my_pack" / "plugin.yaml",
        """
name: my_pack
version: 1.0.0
license: MIT
module: tmp_pkg.my_pack.main
register: register
""".strip()
        + "\n",
    )
    # Overlay state: enabled=true, no signature
    (repo / "data").mkdir(parents=True, exist_ok=True)
    (repo / "data" / "packs_state.json").write_text(
        json.dumps({"my_pack": {"enabled": True}}, indent=2), encoding="utf-8"
    )

    vio, warn = check(repo_root=repo)
    assert not vio
    assert any("enabled without installed signature" in w for w in warn), warn


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
