#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/boundary/test_boundary_snapshot_diff.py         |
# | ROLE: Project test module.                                  |
# | PLIK: tests/boundary/test_boundary_snapshot_diff.py         |
# | ROLA: Moduł testów projektu.                                |
# +-------------------------------------------------------------+

"""
PL: Testy snapshot/diff Boundary na katalogach tymczasowych.
EN: Boundary snapshot/diff tests on temporary directories.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from pathlib import Path
import tempfile

from core.boundary.snapshot import compute_snapshot
from scripts.boundary_diff import diff_snapshots


def _write(p: Path, data: bytes) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data)


def test_boundary_snapshot_and_diff_identical_then_different() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        base_dir = Path(tmp) / "pco"
        # shard-0 (implicit): create one file
        _write(base_dir / "a.json", b"{}")

        snap_a = compute_snapshot(base_dir)
        snap_b = compute_snapshot(base_dir)

        # identical
        rep_same = diff_snapshots(snap_a, snap_b)
        assert rep_same["status"] == "IDENTICAL"
        assert rep_same["changed"] == []

        # mutate: add file
        _write(base_dir / "b.json", b"{}")
        snap_c = compute_snapshot(base_dir)

        rep_diff = diff_snapshots(snap_a, snap_c)
        assert rep_diff["status"] == "DIFFERENT"
        # expect at least shard-0 changed
        assert "shard-0" in rep_diff["changed"]
