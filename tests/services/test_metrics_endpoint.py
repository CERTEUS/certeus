#!/usr/bin/env python3

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_metrics_endpoint.py             |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_metrics_endpoint.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

from __future__ import annotations

from fastapi.testclient import TestClient

from services.api_gateway.main import app


def test_metrics_endpoint_available() -> None:
    client = TestClient(app)

    r = client.get("/metrics")

    assert r.status_code == 200

    text = r.text

    # Basic presence of our SLO metric names (may be zero)

    assert "certeus_ece" in text

    assert "certeus_brier" in text

    assert "certeus_abstain_rate" in text
