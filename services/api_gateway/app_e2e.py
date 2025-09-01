#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/app_e2e.py                     |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/app_e2e.py                     |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/services/api_gateway/app_e2e.py         |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


"""

PL: Moduł systemu CERTEUS.

EN: CERTEUS system module.

"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from fastapi import FastAPI
from pydantic import BaseModel, Field

from kernel.truth_engine import DualCoreVerifier
from services.exporter_service.exporter import ExporterService

__all__ = ["app"]


# ──────────────────────────────────────────────────────────────────────

# App & services

# ──────────────────────────────────────────────────────────────────────


app = FastAPI(title="CERTEUS E2E", version="1.1.0")


# Provide explicit constructor args (fixes: missing template_dir/output_dir)

_exporter = ExporterService(template_dir="templates", output_dir="exports/e2e")

_verifier = DualCoreVerifier()


# ──────────────────────────────────────────────────────────────────────

# Schemas

# ──────────────────────────────────────────────────────────────────────


class SimpleFact(BaseModel):
    """Minimalny model wejściowy do E2E solve."""

    case_id: str = Field(..., description="Case identifier")

    smt2: str = Field(..., description="SMT-LIB2 formula")

    export: bool = Field(False, description="Export report file after solve")

    force_mismatch: bool = Field(False, description="Flip Core-2 to trigger mismatch protocol (testing)")


class SolveResponse(BaseModel):
    status: str

    time_ms: float | None = None

    model: dict[str, Any] | None = None

    error: str | None = None

    report_path: str | None = None

    version: str | None = None


# ──────────────────────────────────────────────────────────────────────

# Routes

# ──────────────────────────────────────────────────────────────────────


@app.get("/health")
def health() -> dict[str, Any]:
    return {"status": "ok", "services": ["verifier", "exporter"]}


@app.post("/e2e/solve", response_model=SolveResponse)
def e2e_solve(payload: SimpleFact) -> SolveResponse:
    # 1) verify with DualCore

    result = _verifier.verify(
        payload.smt2,
        lang="smt2",
        case_id=payload.case_id,
        force_mismatch=payload.force_mismatch,
    )

    # 2) optional export

    report_path: str | None = None

    if payload.export:
        out_path = _exporter.export_report(payload.case_id, result)

        report_path = str(Path(out_path))

    return SolveResponse(
        status=str(result.get("status", "unknown")),
        time_ms=result.get("time_ms"),
        model=result.get("model"),
        error=result.get("error"),
        report_path=report_path,
        version=result.get("version"),
    )
