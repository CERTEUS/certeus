#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: runtime/p2p_transport.py                             |
# | ROLE: QUIC/Noise transport stub + SPIFFE id (CI-friendly)  |
# | PLIK: runtime/p2p_transport.py                             |
# | ROLA: Stub transport QUIC/Noise + SPIFFE id (bez sieci)    |
# +-------------------------------------------------------------+

"""
PL: Minimalna, lokalna warstwa transportowa (stub) imitująca QUIC/Noise.
    Bez sieci: peer→peer w pamięci, kolejki i sesje są lokalne.
    SPIFFE/SPIRE: generujemy syntetyczne identity URI spiffe://certeus/ns/default/peer/<id>.

EN: Minimal, local transport layer (stub) mimicking QUIC/Noise.
    No networking: in-memory peer→peer; queues/sessions are local only.
    SPIFFE/SPIRE: generate synthetic identity URIs spiffe://certeus/ns/default/peer/<id>.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Peer:
    peer_id: str
    spiffe_id: str


class Transport:
    def __init__(self) -> None:
        self._peers: dict[str, Peer] = {}
        self._mailbox: dict[tuple[str, str], list[bytes]] = {}

    def create_peer(self, peer_id: str) -> Peer:
        spiffe = f"spiffe://certeus/ns/default/peer/{peer_id}"
        p = Peer(peer_id=peer_id, spiffe_id=spiffe)
        self._peers[peer_id] = p
        return p

    def dial(self, src: str, dst: str) -> bool:
        return dst in self._peers and src in self._peers

    def send(self, src: str, dst: str, payload: bytes) -> None:
        if not self.dial(src, dst):
            raise RuntimeError("peer not reachable")
        mb = self._mailbox.setdefault((dst, src), [])
        mb.append(bytes(payload))

    def recv(self, dst: str, src: str) -> bytes | None:
        mb = self._mailbox.get((dst, src))
        if not mb:
            return None
        return mb.pop(0)


def echo_roundtrip(msg: str = "synapse") -> dict[str, Any]:
    t = Transport()
    a = t.create_peer("A")
    b = t.create_peer("B")
    assert t.dial(a.peer_id, b.peer_id)
    t.send(a.peer_id, b.peer_id, msg.encode("utf-8"))
    got = t.recv(b.peer_id, a.peer_id)
    return {
        "a": a.spiffe_id,
        "b": b.spiffe_id,
        "ok": got == msg.encode("utf-8"),
        "len": len(got or b""),
    }
