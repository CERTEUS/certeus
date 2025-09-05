#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/security/test_proof_only_middleware.py         |

# | ROLE: Test module.                                          |

# | PLIK: tests/security/test_proof_only_middleware.py         |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Test zapewniający, że Proof-Only middleware wymaga tokenu PCO.

EN: Ensures Proof-Only middleware requires a PCO token.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import importlib
import sys

from fastapi.testclient import TestClient

# === TESTY / TESTS ===

def test_protected_post_requires_pco_token(monkeypatch) -> None:
    # Enforce Proof-Only I/O before app import
    monkeypatch.setenv("STRICT_PROOF_ONLY", "1")
    # Ensure module reloading picks up env
    if "services.api_gateway.main" in sys.modules:
        del sys.modules["services.api_gateway.main"]
    main_mod = importlib.import_module("services.api_gateway.main")

    app = main_mod.app
    client = TestClient(app)

    # Minimal valid body for /v1/pco/bundle to avoid 422 if middleware lets it through
    payload = {
        "rid": "RID-1",
        "smt2_hash": "0" * 64,
        "lfsc": "()",
        "merkle_proof": [],
        "smt2": "()",
    }

    # No token => 403 DROP
    r = client.post("/v1/pco/bundle", json=payload)
    assert r.status_code == 403
    assert "DROP" in r.text
