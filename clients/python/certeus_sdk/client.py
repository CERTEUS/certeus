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

from typing import Any

import requests

# === KONFIGURACJA / CONFIGURATION ===
DEFAULT_BASE_URL = "http://127.0.0.1:8000"


class CerteusClient:
    """PL: Klient HTTP dla CERTEUS.

    EN: HTTP client for CERTEUS.
    """

    def __init__(self, base_url: str = DEFAULT_BASE_URL, *, tenant_id: str | None = None, timeout: float = 15.0):
        self.base_url = base_url.rstrip("/")
        self.session = requests.Session()
        self.timeout = timeout
        if tenant_id:
            self.session.headers["X-Tenant-ID"] = tenant_id

    # === LOGIKA / LOGIC ===
    def _url(self, path: str) -> str:
        return f"{self.base_url}{path}"

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
        r = self.session.post(self._url("/v1/pco/bundle"), json=payload, timeout=self.timeout)
        r.raise_for_status()
        return r.json()

    # --- Analyze / Preview (minimal) ---
    def analyze(self, case_id: str, file_path: str) -> dict[str, Any]:
        with open(file_path, "rb") as fh:
            files = {"file": (file_path.split("/")[-1], fh, "application/octet-stream")}
            r = self.session.post(self._url(f"/v1/analyze?case_id={case_id}"), files=files, timeout=self.timeout)
        r.raise_for_status()
        return r.json()

    def preview(self, file_path: str) -> dict[str, Any]:
        with open(file_path, "rb") as fh:
            files = {"file": (file_path.split("/")[-1], fh, "application/octet-stream")}
            r = self.session.post(self._url("/v1/preview"), files=files, timeout=self.timeout)
        r.raise_for_status()
        return r.json()


# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===
