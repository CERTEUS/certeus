#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/metrics.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/metrics.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""
PL: Router FastAPI dla obszaru metryki Prometheus.

EN: FastAPI router for Prometheus metrics.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi import APIRouter, Response
from prometheus_client import CONTENT_TYPE_LATEST, generate_latest

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

router = APIRouter(prefix="", tags=["metrics"])

# === I/O / ENDPOINTS ===


@router.get("/metrics")
def metrics() -> Response:
    # Use the default global registry

    data = generate_latest()  # type: ignore[arg-type]

    return Response(
        content=data,
        media_type=CONTENT_TYPE_LATEST,
        headers={"Cache-Control": "no-store"},
    )


@router.get("/v1/metrics/summary", summary="Quick in-proc metrics summary")
def metrics_summary() -> dict[str, object]:
    """PL: Zwraca szybkie podsumowanie ścieżek (top avg/count) do widgetów landing.

    EN: Returns a quick summary of paths (top avg/count) for landing widgets.
    """

    try:
        from monitoring.metrics_slo import http_summary

        return http_summary(10)
    except Exception:
        return {"top_avg_ms": [], "top_count": [], "total_paths": 0}


@router.get("/v1/metrics/series", summary="Quick series for top endpoints")
def metrics_series(top: int = 5) -> dict[str, object]:
    try:
        from monitoring.metrics_slo import http_series

        return http_series(top)
    except Exception:
        return {"series": []}


# === TESTY / TESTS ===
