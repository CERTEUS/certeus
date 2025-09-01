#!/usr/bin/env python3

"""
PL: Router FastAPI dla obszaru metryki Prometheus.

EN: FastAPI router for Prometheus metrics.
"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/metrics.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/metrics.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

from fastapi import APIRouter, Response
from prometheus_client import CONTENT_TYPE_LATEST, generate_latest

router = APIRouter(prefix="", tags=["metrics"])


@router.get("/metrics")
def metrics() -> Response:
    # Use the default global registry

    data = generate_latest()  # type: ignore[arg-type]

    return Response(content=data, media_type=CONTENT_TYPE_LATEST)
