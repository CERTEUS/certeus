#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: clients/python/certeus_sdk/client.py                 |
# | ROLE: Python SDK client.                                     |
# | PLIK: clients/python/certeus_sdk/client.py                 |
# | ROLA: Klient SDK w Pythonie.                                 |
# +-------------------------------------------------------------+
"""
PL: Klient SDK w Pythonie — cienki wrapper HTTP nad API Gateway CERTEUS.

EN: Python SDK client — thin HTTP wrapper over CERTEUS API Gateway.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections.abc import Callable
from typing import Any

import requests

# === KONFIGURACJA / CONFIGURATION ===
DEFAULT_BASE_URL = "http://127.0.0.1:8000"


class CerteusClient:
    """PL: Klient HTTP dla CERTEUS.

    EN: HTTP client for CERTEUS.
    """

    def __init__(
        self,
        base_url: str = DEFAULT_BASE_URL,
        *,
        tenant_id: str | None = None,
        timeout: float = 15.0,
        retries: int = 2,
        backoff_sec: float = 0.2,
        idem_key_factory: Callable[[], str] | None = None,
    ):
        self.base_url = base_url.rstrip("/")
        self.session = requests.Session()
        self.timeout = timeout
        self.retries = max(0, int(retries))
        self.backoff_sec = float(backoff_sec)
        self.idem_key_factory = idem_key_factory
        if tenant_id:
            self.session.headers["X-Tenant-ID"] = tenant_id

    # === LOGIKA / LOGIC ===
    def _url(self, path: str) -> str:
        return f"{self.base_url}{path}"

    def _with_idem(self, headers: dict[str, str] | None = None) -> dict[str, str]:
        h: dict[str, str] = dict(headers or {})
        if self.idem_key_factory is not None:
            try:
                key = self.idem_key_factory()
                if key:
                    h.setdefault("Idempotency-Key", key)
            except Exception:
                pass
        return h

    def _post(
        self,
        path: str,
        *,
        json_body: Any | None = None,
        files: Any | None = None,
        headers: dict[str, str] | None = None,
    ):
        import time

        last_exc: Exception | None = None
        h = self._with_idem(headers)
        for attempt in range(self.retries + 1):
            try:
                if files is not None:
                    r = self.session.post(self._url(path), files=files, headers=h, timeout=self.timeout)
                else:
                    r = self.session.post(self._url(path), json=json_body, headers=h, timeout=self.timeout)
                r.raise_for_status()
                return r
            except Exception as e:  # noqa: BLE001 - SDK toleruje sieć
                last_exc = e
                if attempt >= self.retries:
                    raise
                time.sleep(self.backoff_sec * (2**attempt))
        assert last_exc is not None
        raise last_exc

    # --- System / Meta ---
    def openapi(self) -> dict[str, Any]:
        r = self.session.get(self._url("/openapi.json"), timeout=self.timeout)
        r.raise_for_status()
        return r.json()

    def health(self) -> dict[str, Any]:
        r = self.session.get(self._url("/health"), timeout=self.timeout)
        r.raise_for_status()
        return r.json()

    # --- PCO ---
    def get_public_pco(self, case_id: str) -> dict[str, Any]:
        r = self.session.get(self._url(f"/pco/public/{case_id}"), timeout=self.timeout)
        r.raise_for_status()
        return r.json()

    def publish_pco_bundle(
        self,
        *,
        rid: str,
        smt2_hash: str,
        lfsc: str,
        drat: str | None = None,
        merkle_proof: list[dict[str, str]] | None = None,
        smt2: str | None = None,
    ) -> dict[str, Any]:
        """PL: Publikuje ProofBundle (v0.2). Wymaga klucza ED25519 po stronie serwera.

        EN: Publishes ProofBundle (v0.2). Requires ED25519 key server-side.
        """
        payload: dict[str, Any] = {
            "rid": rid,
            "smt2_hash": smt2_hash,
            "lfsc": lfsc,
        }
        if drat is not None:
            payload["drat"] = drat
        if merkle_proof is not None:
            payload["merkle_proof"] = merkle_proof
        if smt2 is not None:
            payload["smt2"] = smt2
        r = self._post("/v1/pco/bundle", json_body=payload)
        r.raise_for_status()
        return r.json()

    # --- Analyze / Preview (minimal) ---
    def analyze(self, case_id: str, file_path: str) -> dict[str, Any]:
        with open(file_path, "rb") as fh:
            files = {"file": (file_path.split("/")[-1], fh, "application/octet-stream")}
            r = self._post(f"/v1/analyze?case_id={case_id}", files=files)
        r.raise_for_status()
        return r.json()

    def preview(self, file_path: str) -> dict[str, Any]:
        with open(file_path, "rb") as fh:
            files = {"file": (file_path.split("/")[-1], fh, "application/octet-stream")}
            r = self._post("/v1/preview", files=files)
        r.raise_for_status()
        return r.json()

    # --- Billing (first-class) ---
    def get_balance(self) -> dict[str, Any]:
        r = self.session.get(self._url("/v1/billing/balance"), timeout=self.timeout)
        r.raise_for_status()
        return r.json()

    def allocate(self, units: int) -> dict[str, Any]:
        r = self._post("/v1/billing/allocate", json_body={"units": int(units)})
        r.raise_for_status()
        return r.json()

    def refund(self, tenant: str, units: int) -> dict[str, Any]:
        r = self._post("/v1/billing/refund", json_body={"tenant": tenant, "units": int(units)})
        r.raise_for_status()
        return r.json()

    def set_quota(self, tenant: str, units: int) -> dict[str, Any]:
        r = self._post("/v1/billing/quota", json_body={"tenant": tenant, "units": int(units)})
        r.raise_for_status()
        return r.json()


# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
