"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""


# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_limits.py                       |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_limits.py                       |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE / PLIK: tests/services/test_limits.py                          |

# | ROLE / ROLA:                                                         |

# |  EN: Unit tests for per-tenant limits hook (budget/rate).           |

# |  PL: Testy jednostkowe hooka limitów per-tenant (budżet/limit).     |

# +=====================================================================+

from __future__ import annotations

from fastapi import HTTPException
import pytest
from starlette.requests import Request  # FastAPI re-exports this class

from services.api_gateway.limits import enforce_limits, get_tenant_id, set_tenant_quota


def _make_request(headers: dict[str, str] | None = None) -> Request:
    """

    EN: Build a real Starlette/FastAPI Request from raw ASGI scope.

    PL: Zbuduj realny obiekt Request na bazie surowego scope ASGI.

    """

    raw = []

    if headers:
        for k, v in headers.items():
            raw.append((k.lower().encode("ascii"), v.encode("utf-8")))

    scope = {"type": "http", "headers": raw}

    return Request(scope)  # type: ignore[arg-type]


def test_get_tenant_id_header_and_fallback() -> None:
    """

    EN: Extract tenant from header; fallback to 'anonymous'.

    PL: Pobiera tenant z nagłówka; w przeciwnym razie 'anonymous'.

    """

    r1 = _make_request({"X-Tenant-ID": "t-42"})

    assert get_tenant_id(r1) == "t-42"

    r2 = _make_request()

    assert get_tenant_id(r2) == "anonymous"


def test_enforce_limits_success_and_exhaustion() -> None:
    """

    EN: Budget charges succeed until exhausted; next call raises 429.

    PL: Pobrania z budżetu działają do wyczerpania; kolejny wywołuje 429.

    """

    tenant = "t-budget"

    set_tenant_quota(tenant, 2)

    r = _make_request({"X-Tenant-ID": tenant})

    # dwa zużycia — OK

    enforce_limits(r, cost_units=1)

    enforce_limits(r, cost_units=1)

    # trzecie powinno przerwać

    with pytest.raises(HTTPException) as ex:
        enforce_limits(r, cost_units=1)

    assert ex.value.status_code == 429
