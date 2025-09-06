#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/gates/test_supply_chain_enforce_enterprise.py  |
# | ROLE: Enterprise tests: supply-chain enforce (repo+plugins)|
# +-------------------------------------------------------------+

from __future__ import annotations

import json
from pathlib import Path

from scripts.gates.supply_chain_enforce import main as gate_main


def _mk_plugin(
    root: Path, name: str, *, with_sbom: bool, with_prov: bool, with_sig: bool
) -> Path:
    d = root / "plugins" / name
    (d).mkdir(parents=True, exist_ok=True)
    (d / "plugin.yaml").write_text(f"name: {name}\n", encoding="utf-8")
    sc = d / "supply_chain"
    sc.mkdir(exist_ok=True)
    if with_sbom:
        (sc / "sbom.cdx.json").write_text("{}", encoding="utf-8")
    if with_prov:
        (sc / "provenance.json").write_text("{}", encoding="utf-8")
    if with_sig:
        (sc / "bundle.sig").write_text("sig", encoding="utf-8")
        (sc / "bundle.cert").write_text("cert", encoding="utf-8")
    return d


def test_supply_chain_enforce_repo_only(tmp_path: Path, monkeypatch) -> None:
    # No repo SBOM → ok unless SUPPLY_CHAIN_ENFORCE=1
    monkeypatch.chdir(tmp_path)
    rc = gate_main()
    assert rc == 0
    # Enforce → fail without repo sbom/artifact
    monkeypatch.setenv("SUPPLY_CHAIN_ENFORCE", "1")
    rc2 = gate_main()
    assert rc2 == 1


def test_supply_chain_enforce_plugins_deny_by_default(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.chdir(tmp_path)
    # Repo SBOM present to isolate plugin checks
    (tmp_path / "sbom.json").write_text("{}", encoding="utf-8")
    # Plugin A complete (sbom+provenance)
    _mk_plugin(tmp_path, "pluginA", with_sbom=True, with_prov=True, with_sig=False)
    # Plugin B missing provenance
    _mk_plugin(tmp_path, "pluginB", with_sbom=True, with_prov=False, with_sig=False)
    # Enforce deny-by-default
    monkeypatch.setenv("SUPPLY_CHAIN_ENFORCE", "1")
    rc = gate_main()
    assert rc == 1  # violations present
    rep = json.loads(
        (tmp_path / "out" / "supply_chain_enforce.json").read_text(encoding="utf-8")
    )
    assert isinstance(rep.get("violations"), list) and any(
        "pluginB" in x for x in rep.get("violations")
    )


def test_supply_chain_enforce_require_cosign(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.chdir(tmp_path)
    (tmp_path / "sbom.json").write_text("{}", encoding="utf-8")
    # Plugin C has sbom+prov but no sigs → fail when REQUIRE_COSIGN=1
    _mk_plugin(tmp_path, "pluginC", with_sbom=True, with_prov=True, with_sig=False)
    monkeypatch.setenv("SUPPLY_CHAIN_ENFORCE", "1")
    monkeypatch.setenv("REQUIRE_COSIGN", "1")
    rc = gate_main()
    assert rc == 1
    rep = json.loads(
        (tmp_path / "out" / "supply_chain_enforce.json").read_text(encoding="utf-8")
    )
    assert any("missing cosign" in x for x in rep.get("violations", []))
