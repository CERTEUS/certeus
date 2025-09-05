#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/otel/mock_otlp.py                            |
# | ROLE: Minimal OTLP HTTP receiver (dev/CI)                    |
# | PLIK: scripts/otel/mock_otlp.py                            |
# | ROLA: Minimalny odbiornik OTLP HTTP (dev/CI)                 |
# +-------------------------------------------------------------+

"""
PL: Minimalny serwer OTLP (HTTP) do testów/CI. Odbiera POST /v1/traces
    i zwraca 200. Nie zapisuje trwałych danych.

EN: Minimal OTLP HTTP receiver for tests/CI. Accepts POST /v1/traces
    and responds 200. No persistent storage.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from http.server import BaseHTTPRequestHandler, HTTPServer
import threading
import time

class _Handler(BaseHTTPRequestHandler):  # pragma: no cover - simple stub
    def do_POST(self):  # noqa: N802
        if self.path == "/v1/traces":
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(b"{}")
        else:
            self.send_response(404)
            self.end_headers()

    def log_message(self, fmt, *args):  # quiet
        return

def main() -> int:
    host, port = "127.0.0.1", 4318
    httpd = HTTPServer((host, port), _Handler)
    t = threading.Thread(target=httpd.serve_forever, daemon=True)
    t.start()
    # Run for a short time (default 120s) or until interrupted
    timeout = 120.0
    start = time.perf_counter()
    try:
        while time.perf_counter() - start < timeout:
            time.sleep(0.5)
    except KeyboardInterrupt:
        pass
    httpd.shutdown()
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
