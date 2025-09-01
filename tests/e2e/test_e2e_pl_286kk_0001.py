# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/e2e/test_e2e_pl_286kk_0001.py                 |

# | ROLE: Project module.                                       |

# | PLIK: tests/e2e/test_e2e_pl_286kk_0001.py                 |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

CERTEUS — E2E Test: Art. 286 k.k.

PL: Test end-to-end kanonicznego przypadku oszustwa dla /v1/analyze.

EN: End-to-end test of canonical fraud case via /v1/analyze.

"""

import io

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_full_analysis_returns_sat():
    payload = ("dowody.pdf", io.BytesIO(b"fake bytes"), "application/pdf")

    r = client.post("/v1/analyze?case_id=pl-286kk-0001", files={"file": payload})

    assert r.status_code == 200

    data = r.json()

    assert data["case_id"] == "pl-286kk-0001"

    assert data["analysis_result"]["status"] == "sat"

    assert "model" in data["analysis_result"]
