#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: clients/sdk/python/certeus_sdk/__init__.py            |
# | ROLE: Python SDK module.                                    |
# | PLIK: clients/sdk/python/certeus_sdk/__init__.py            |
# | ROLA: Moduł SDK Python.                                     |
# +-------------------------------------------------------------+

"""
CERTEUS Python SDK (lightweight)

PL: Lekki klient HTTP dla kluczowych endpointów (Devices, Packs, Billing).
EN: Lightweight HTTP client for key endpoints (Devices, Packs, Billing).
"""

from __future__ import annotations

from typing import Any

# === IMPORTY / IMPORTS ===

import httpx

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

class CerteusClient:
    def __init__(
        self,
        base_url: str = "http://127.0.0.1:8000",
        *,
        headers: dict[str, str] | None = None,
        timeout: float = 10.0,
    ) -> None:
        self.base_url = base_url.rstrip("/")
        self.headers = dict(headers or {})
        self._client = httpx.Client(timeout=timeout)

    # --- Generic ---
    def get(self, path: str, params: dict[str, Any] | None = None) -> httpx.Response:
        return self._client.get(f"{self.base_url}{path}", headers=self.headers, params=params)

    def post(self, path: str, json: dict[str, Any] | None = None) -> httpx.Response:
        return self._client.post(f"{self.base_url}{path}", headers=self.headers, json=json)

    # --- Devices ---
    def devices_hde_plan(self, case: str, target_horizon: float = 0.2) -> dict[str, Any]:
        r = self.post("/v1/devices/horizon_drive/plan", {"case": case, "target_horizon": target_horizon})
        r.raise_for_status()
        return r.json()

    def devices_qoracle_expectation(
        self, *, question: str | None = None, constraints: dict[str, Any] | None = None
    ) -> dict[str, Any]:
        payload = {"question": question, "constraints": constraints}
        r = self.post("/v1/devices/qoracle/expectation", payload)
        r.raise_for_status()
        return r.json()

    def devices_entangle(self, variables: list[str], target_negativity: float = 0.1) -> dict[str, Any]:
        r = self.post("/v1/devices/entangle", {"variables": variables, "target_negativity": target_negativity})
        r.raise_for_status()
        return r.json()

    def devices_chronosync_reconcile(
        self, coords: dict[str, Any], pc_delta: dict[str, Any] | None = None
    ) -> dict[str, Any]:
        r = self.post("/v1/devices/chronosync/reconcile", {"coords": coords, "pc_delta": pc_delta})
        r.raise_for_status()
        return r.json()

    # --- Packs / Marketplace ---
    def packs_list(self) -> list[dict[str, Any]]:
        r = self.get("/v1/packs/")
        r.raise_for_status()
        return r.json()

    def packs_enable(self, pack: str, enabled: bool) -> dict[str, Any]:
        r = self.post("/v1/packs/enable", {"pack": pack, "enabled": bool(enabled)})
        r.raise_for_status()
        return r.json()

    def packs_install(self, pack: str, signature: str, version: str | None = None) -> dict[str, Any]:
        payload: dict[str, Any] = {"pack": pack, "signature": signature}
        if version:
            payload["version"] = version
        r = self.post("/v1/packs/install", payload)
        r.raise_for_status()
        return r.json()

    # --- Billing ---
    def billing_quota(self, tenant: str | None = None) -> dict[str, Any]:
        # Tenant selected via headers (X-Tenant-ID); optional param for helper
        r = self.get("/v1/billing/quota")
        r.raise_for_status()
        return r.json()

    def billing_set_quota(self, units: int, tenant: str | None = None) -> dict[str, Any]:
        r = self.post("/v1/billing/quota", {"tenant": tenant, "units": units})
        r.raise_for_status()
        return r.json()

    def billing_allocate(self, cost_units: int) -> dict[str, Any]:
        r = self.post("/v1/billing/allocate", {"cost_units": cost_units})
        r.raise_for_status()
        return r.json()

    def billing_refund(self, units: int) -> dict[str, Any]:
        r = self.post("/v1/billing/refund", {"units": units})
        r.raise_for_status()
        return r.json()

    # --- FIN tokens demo ---
    def fin_tokens_request(self, user_id: str, amount: int, purpose: str | None = None) -> dict[str, Any]:
        r = self.post("/v1/fin/tokens/request", {"user_id": user_id, "amount": amount, "purpose": purpose})
        r.raise_for_status()
        return r.json()

    def fin_tokens_allocate(self, request_id: str, allocated_by: str | None = None) -> dict[str, Any]:
        r = self.post("/v1/fin/tokens/allocate", {"request_id": request_id, "allocated_by": allocated_by})
        r.raise_for_status()
        return r.json()

    def fin_tokens_status(self, request_id: str) -> dict[str, Any]:
        r = self.get(f"/v1/fin/tokens/{request_id}")
        r.raise_for_status()
        return r.json()

    def close(self) -> None:
        try:
            self._client.close()
        except Exception:
            pass

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
