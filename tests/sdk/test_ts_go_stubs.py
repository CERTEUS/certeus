#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/sdk/test_ts_go_stubs.py                        |
# | ROLE: Enterprise tests: TS/Go SDK stubs surface            |
# +-------------------------------------------------------------+

from __future__ import annotations

from pathlib import Path


def test_ts_sdk_has_core_and_p2p_methods() -> None:
    p = Path("sdk/ts/src/client.ts")
    assert p.exists()
    s = p.read_text(encoding="utf-8")
    # Core PFS
    assert "pfsList(" in s
    assert "pfsXattrs(" in s
    assert "publish(" in s
    # P2P
    assert "transportEcho(" in s or "p2pEnqueue(" in s


def test_go_sdk_has_core_and_p2p_methods() -> None:
    p = Path("sdk/go/certeus/certeus.go")
    assert p.exists()
    s = p.read_text(encoding="utf-8")
    assert "func (c *Client) PFSList(" in s
    assert "func (c *Client) PFSXattrs(" in s
    assert "func (c *Client) Publish(" in s
    assert "P2PTransportEcho(" in s or "P2PEnqueue(" in s
