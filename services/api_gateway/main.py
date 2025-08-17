#!/usr/bin/env python3
# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/api_gateway/main.py            |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+

# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/services/api_gateway/main.py    |
# | DATE:    2025-08-17                                          |
# +=====================================================================+
"""
PL: Moduł systemu CERTEUS.
EN: CERTEUS system module.
"""

# -*- coding: utf-8 -*-
# +=====================================================================+
# |                           CERTEUS                                   |
# |                     API Gateway (FastAPI)                           |
# +=====================================================================+
# | MODULE:  services/api_gateway/main.py                               |
# | VERSION: 1.1.3                                                      |
# | DATE:    2025-08-16                                                 |
# +=====================================================================+
# | ROLE: Mount all routers available in the repo structure.            |
# +=====================================================================+

from __future__ import annotations

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

# istniejące routery w repo
from services.api_gateway.routers import verify
from services.api_gateway.routers import mismatch
from services.api_gateway.routers import export
from services.api_gateway.routers import ledger
from services.api_gateway.routers import (
    system,
)  # tu dorzucimy /v1/ingest,/v1/analyze,/v1/sipp

app = FastAPI(title="CERTEUS API Gateway", version="1.1.3")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# montowanie routerów, tylko te które faktycznie istnieją w repo
app.include_router(verify.router)
app.include_router(mismatch.router)
app.include_router(export.router)
app.include_router(ledger.router)
app.include_router(system.router)  # zawiera ingest/analyze/sipp


@app.get("/health")
def health() -> dict[str, object]:
    return {"status": "ok"}
