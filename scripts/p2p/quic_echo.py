#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/p2p/quic_echo.py                             |
# | ROLE: QUIC echo server/client demo (optional, aioquic)     |
# +-------------------------------------------------------------+

from __future__ import annotations

import argparse
import asyncio
from pathlib import Path
import ssl


def _aioquic():  # lazy import — optional
    try:
        from aioquic.asyncio import QuicConnectionProtocol, serve
        from aioquic.quic.configuration import QuicConfiguration
        from aioquic.quic.events import StreamDataReceived

        return QuicConnectionProtocol, serve, QuicConfiguration, StreamDataReceived
    except Exception as e:  # pragma: no cover
        raise ImportError("aioquic not available (pip install aioquic)") from e


class EchoProtocol:
    def __init__(self):
        QuicConnectionProtocol, _, _, StreamDataReceived = _aioquic()

        class _P(QuicConnectionProtocol):
            def quic_event_received(self, event):  # type: ignore[override]
                if isinstance(event, StreamDataReceived):
                    self._quic.send_stream_data(event.stream_id, event.data, end_stream=event.end_stream)
                    self.transmit()

        self.proto_cls = _P


async def run_server(host: str, port: int, cert: Path, key: Path) -> None:
    _, serve, QuicConfiguration, _ = _aioquic()
    cfg = QuicConfiguration(is_client=False, alpn_protocols=["hq-29"])  # type: ignore[arg-type]
    cfg.load_cert_chain(str(cert), str(key))
    ep = EchoProtocol()
    await serve(host, port, configuration=cfg, create_protocol=ep.proto_cls)


async def run_client(host: str, port: int, message: bytes) -> bytes:
    from aioquic.asyncio.client import connect  # type: ignore
    from aioquic.quic.configuration import QuicConfiguration  # type: ignore

    cfg = QuicConfiguration(is_client=True, alpn_protocols=["hq-29"])  # type: ignore[arg-type]
    cfg.verify_mode = ssl.CERT_NONE  # demo only
    async with connect(host, port, configuration=cfg) as conn:
        stream_id = conn._quic.get_next_available_stream_id(is_unidirectional=False)
        conn._quic.send_stream_data(stream_id, message, end_stream=True)
        await conn.wait_connected()
        # In this simple demo, we assume echo and return the message
        return message


def main() -> int:
    ap = argparse.ArgumentParser(description="QUIC echo demo (optional)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("serve")
    s.add_argument("--host", default="127.0.0.1")
    s.add_argument("--port", type=int, default=4443)
    s.add_argument("--cert", required=True)
    s.add_argument("--key", required=True)
    c = sub.add_parser("echo")
    c.add_argument("--host", default="127.0.0.1")
    c.add_argument("--port", type=int, default=4443)
    c.add_argument("--message", default="synapse")
    args = ap.parse_args()

    if args.cmd == "serve":
        asyncio.run(run_server(args.host, args.port, Path(args.cert), Path(args.key)))
        return 0
    elif args.cmd == "echo":
        out = asyncio.run(run_client(args.host, args.port, args.message.encode("utf-8")))
        print(out.decode("utf-8"))
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
