from __future__ import annotations

import importlib
import sys

from fastapi.testclient import TestClient


def test_security_headers_present(monkeypatch) -> None:
    # Ensure security headers are enabled (default SEC_HEADERS=1)
    if "services.api_gateway.main" in sys.modules:
        del sys.modules["services.api_gateway.main"]
    main_mod = importlib.import_module("services.api_gateway.main")
    client = TestClient(main_mod.app)

    r = client.get("/health")
    assert r.status_code == 200
    # Basic set from middleware
    assert r.headers.get("X-Content-Type-Options") == "nosniff"
    assert r.headers.get("X-Frame-Options") == "DENY"
    assert "Content-Security-Policy" in r.headers
    assert "Strict-Transport-Security" in r.headers


def test_rate_limit_triggers_429(monkeypatch) -> None:
    # Enable simple per-IP rate limit to 1 req/min
    monkeypatch.setenv("RATE_LIMIT_PER_MIN", "1")
    # Reload app to apply env
    if "services.api_gateway.main" in sys.modules:
        del sys.modules["services.api_gateway.main"]
    main_mod = importlib.import_module("services.api_gateway.main")
    client = TestClient(main_mod.app)

    # First request OK
    r1 = client.get("/health")
    assert r1.status_code == 200
    # Second immediately should exceed window and return 429
    r2 = client.get("/health")
    assert r2.status_code == 429
