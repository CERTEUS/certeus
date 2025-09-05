"""
Tests for Plugin Supply-Chain Gate (report-only by default).
"""

from __future__ import annotations

from pathlib import Path

from scripts.gates import plugin_supply_chain_gate as gate


def _write_plugin(tmp: Path, name: str, with_artifacts: bool = False) -> Path:
    pdir = tmp / "plugins" / name
    pdir.mkdir(parents=True, exist_ok=True)
    (pdir / "plugin.yaml").write_text(
        f"""
name: {name}
version: 0.1.0
license: MIT
""".strip(),
        encoding="utf-8",
    )
    if with_artifacts:
        (pdir / "sbom.cdx.json").write_text("{}", encoding="utf-8")
        (pdir / "provenance.json").write_text("{}", encoding="utf-8")
    return pdir


def test_gate_reports_missing_artifacts(tmp_path: Path) -> None:
    _write_plugin(tmp_path, "demo_missing", with_artifacts=False)
    vio, warn = gate.check(tmp_path)
    assert any("missing SBOM" in v for v in vio)
    assert any("missing provenance" in v for v in vio)
    # cosign is optional → warning allowed
    assert any("cosign signatures" in w for w in warn)


def test_gate_ok_when_artifacts_present(tmp_path: Path) -> None:
    _write_plugin(tmp_path, "demo_ok", with_artifacts=True)
    vio, warn = gate.check(tmp_path)
    assert vio == []
    # cosign optional → may still warn if not present
    assert warn == ["demo_ok: cosign signatures not found (optional: *.sig/*.cert)"]
