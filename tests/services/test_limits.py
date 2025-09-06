#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_limits.py                        |
# | ROLE: Limits/token-bucket tests                             |
# | PLIK: tests/services/test_limits.py                        |
# | ROLA: Testy limitów/token-bucket                            |
# +-------------------------------------------------------------+
"""
PL: Testy przeciążeniowe (MVP): budżet jednostek i odpowiedź 429 przy przekroczeniu.

EN: Overload tests (MVP): unit budget and 429 on exceeding it.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from fastapi import HTTPException
import pytest
from starlette.requests import Request

from services.api_gateway.limits import (
    enforce_limits,
    get_tenant_balance,
    set_tenant_quota,
)


def _req_for(tenant: str) -> Request:
    scope = {"type": "http", "headers": [(b"x-tenant-id", tenant.encode("utf-8"))]}
    return Request(scope)  # type: ignore[arg-type]


def test_limits_enforce_429_on_budget_exceeded() -> None:
    tenant = "t-limit"
    set_tenant_quota(tenant, 2)
    assert get_tenant_balance(tenant) >= 2

    r = _req_for(tenant)
    enforce_limits(r, cost_units=1)
    enforce_limits(r, cost_units=1)
    with pytest.raises(HTTPException) as ex:
        enforce_limits(r, cost_units=1)
    assert ex.value.status_code == 429
