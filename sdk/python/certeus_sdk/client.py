#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: sdk/python/certeus_sdk/client.py                    |
# | ROLE: Project module.                                       |
# | PLIK: sdk/python/certeus_sdk/client.py                    |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Minimalny klient HTTP dla CERTEUS (QTMP i lexqft). Bez zależności poza `requests`.
EN: Minimal HTTP client for CERTEUS (QTMP and lexqft). Uses `requests` only.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

import requests

# === KONFIGURACJA / CONFIGURATION ===

DEFAULT_BASE_URL = "http://127.0.0.1:8000"


# === MODELE / MODELS ===


@dataclass(slots=True)
class SDKResponse:
    ok: bool
    status: int
    data: Any
    pco_headers: dict[str, str]


# === LOGIKA / LOGIC ===


class CerteusClient:
    """
    PL: Synchroniczny klient SDK (MVP). Obsługuje kluczowe ścieżki QTMP i lexqft.
    EN: Synchronous SDK client (MVP). Supports key QTMP and lexqft endpoints.
    """

    def __init__(self, base_url: str = DEFAULT_BASE_URL, session: requests.Session | None = None) -> None:
        self.base_url = base_url.rstrip("/")
        self._s = session or requests.Session()

    # --- Pomocnicze ---------------------------------------------------------

    @staticmethod
    def _extract_pco_headers(headers: Mapping[str, str]) -> dict[str, str]:
        return {k: v for k, v in headers.items() if k.startswith("X-CERTEUS-PCO-")}

    def _post(self, path: str, json: Any | None = None) -> SDKResponse:
        r = self._s.post(f"{self.base_url}{path}", json=json)
        data: Any
        try:
            data = r.json()
        except Exception:
            data = None
        return SDKResponse(ok=r.ok, status=r.status_code, data=data, pco_headers=self._extract_pco_headers(r.headers))

    def _get(self, path: str) -> SDKResponse:
        r = self._s.get(f"{self.base_url}{path}")
        data: Any
        try:
            data = r.json()
        except Exception:
            data = None
        return SDKResponse(ok=r.ok, status=r.status_code, data=data, pco_headers=self._extract_pco_headers(r.headers))

    # --- QTMP ---------------------------------------------------------------

    def qtm_init_case(
        self, *, case: str | None = None, basis: list[str] | None = None, state_uri: str | None = None
    ) -> SDKResponse:
        payload: dict[str, Any] = {}
        if case:
            payload["case"] = case
        if basis is not None:
            payload["basis"] = basis
        if state_uri:
            payload["state_uri"] = state_uri
        return self._post("/v1/qtm/init_case", json=payload)

    def qtm_measure(
        self, *, operator: str, case: str | None = None, source: str | None = None, basis: list[str] | None = None
    ) -> SDKResponse:
        payload: dict[str, Any] = {"operator": operator}
        if case:
            payload["case"] = case
        if source:
            payload["source"] = source
        if basis is not None:
            payload["basis"] = basis
        return self._post("/v1/qtm/measure", json=payload)

    def qtm_measure_sequence(
        self,
        *,
        operators: list[str],
        case: str | None = None,
        basis: list[str] | None = None,
        no_collapse: bool | None = None,
    ) -> SDKResponse:
        payload: dict[str, Any] = {"operators": operators}
        if case:
            payload["case"] = case
        if basis is not None:
            payload["basis"] = basis
        if no_collapse is not None:
            payload["no_collapse"] = no_collapse
        return self._post("/v1/qtm/measure_sequence", json=payload)

    def qtm_state(self, case: str) -> SDKResponse:
        return self._get(f"/v1/qtm/state/{case}")

    def qtm_operators(self) -> SDKResponse:
        return self._get("/v1/qtm/operators")

    def qtm_uncertainty(self) -> SDKResponse:
        return self._get("/v1/qtm/uncertainty")

    def qtm_decoherence(self, *, case: str | None, channel: str, gamma: float | None = None) -> SDKResponse:
        payload: dict[str, Any] = {"channel": channel}
        if case:
            payload["case"] = case
        if gamma is not None:
            payload["gamma"] = float(gamma)
        return self._post("/v1/qtm/decoherence", json=payload)

    def qtm_preset_save(self, *, case: str, operator: str) -> SDKResponse:
        return self._post("/v1/qtm/preset", json={"case": case, "operator": operator})

    def qtm_preset_get(self, *, case: str) -> SDKResponse:
        return self._get(f"/v1/qtm/preset/{case}")

    def qtm_preset_list(self) -> SDKResponse:
        return self._get("/v1/qtm/presets")

    def qtm_preset_delete(self, *, case: str) -> SDKResponse:
        r = self._s.delete(f"{self.base_url}/v1/qtm/preset/{case}")
        try:
            data = r.json()
        except Exception:
            data = None
        return SDKResponse(ok=r.ok, status=r.status_code, data=data, pco_headers=self._extract_pco_headers(r.headers))

    # --- lexqft -------------------------------------------------------------

    def lexqft_coverage(self) -> SDKResponse:
        return self._get("/v1/lexqft/coverage")

    def lexqft_tunnel(self, *, evidence_energy: float, state_uri: str | None = None) -> SDKResponse:
        payload: dict[str, Any] = {"evidence_energy": float(evidence_energy)}
        if state_uri:
            payload["state_uri"] = state_uri
        return self._post("/v1/lexqft/tunnel", json=payload)

    # --- Ledger -------------------------------------------------------------

    def ledger_records(self, *, case_id: str) -> SDKResponse:
        return self._get(f"/v1/ledger/{case_id}/records")

    # --- ChatOps ------------------------------------------------------------

    def chatops_command(self, *, cmd: str, args: dict | None = None, text_context: str | None = None) -> SDKResponse:
        payload: dict[str, Any] = {"cmd": cmd}
        if args is not None:
            payload["args"] = args
        if text_context:
            payload["text_context"] = text_context
        return self._post("/v1/chatops/command", json=payload)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
