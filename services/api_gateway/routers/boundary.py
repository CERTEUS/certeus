#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/boundary.py            |
# | ROLE: Project module.                                       |
# | PLIK: services/api_gateway/routers/boundary.py            |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla Boundary: status shardów oraz rekonstrukcja.

EN: FastAPI router for Boundary: shard status and reconstruction.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

from fastapi import APIRouter

from core.boundary.reconstruct import bulk_reconstruct

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

router = APIRouter(prefix="/v1/boundary", tags=["boundary"])


def _bundle_dir() -> Path:
    return Path(os.getenv("PROOF_BUNDLE_DIR") or "./data/public_pco")


def _status() -> dict[str, Any]:
    rep = bulk_reconstruct(_bundle_dir())
    rep["anchors"] = {"observed_at": _now_iso()}
    return rep


def _now_iso() -> str:
    import time

    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


# === I/O / ENDPOINTS ===


@router.get("/status")
def get_status() -> dict[str, Any]:
    return _status()


@router.post("/reconstruct")
def reconstruct_now() -> dict[str, Any]:
    # No side-effects yet; returns fresh status
    return _status()


# === TESTY / TESTS ===
