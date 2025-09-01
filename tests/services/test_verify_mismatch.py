# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_verify_mismatch.py              |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_verify_mismatch.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Test symuluje rozbieżność rdzeni i sprawdza odpowiedź 409.

EN: Test simulates core mismatch and checks 409 response.

"""


# === IMPORTY / IMPORTS ===

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# === TEST / TEST ===


def test_verify_returns_409_on_mismatch(monkeypatch):
    """

    PL: Symulowany MismatchError powinien dać 409 + requires_human:true.

    EN: Simulated MismatchError should return 409 + requires_human:true.

    """

    from kernel import truth_engine

    original = truth_engine.DualCoreVerifier.verify

    def fake_verify(self, formula, lang="smt2"):
        from kernel.mismatch_protocol import MismatchError

        raise MismatchError("forced mismatch")

    monkeypatch.setattr(truth_engine.DualCoreVerifier, "verify", fake_verify)

    client = TestClient(app)

    r = client.post("/v1/verify", json={"formula": "(set-logic QF_LIA)", "lang": "smt2"})

    assert r.status_code == 409

    body = r.json()

    assert body["detail"]["requires_human"] is True

    # porządek

    monkeypatch.setattr(truth_engine.DualCoreVerifier, "verify", original)
