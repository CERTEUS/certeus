#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_pnip_strict.py                   |

# | ROLE: Test module.                                          |

# | PLIK: tests/services/test_pnip_strict.py                   |

# | ROLA: Moduł testów.                                         |

# +-------------------------------------------------------------+

"""
PL: Testy ścisłego PNIP — niepoprawny hash i policy powodują 400.

EN: Strict PNIP tests — invalid hash and policy result in 400.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from fastapi.testclient import TestClient

# === TESTY / TESTS ===


def test_publish_reason_pnip_strict_invalid_returns_400(monkeypatch) -> None:
    # STRICT_PNIP on
    monkeypatch.setenv("STRICT_PNIP", "1")

    from services.api_gateway.main import app

    client = TestClient(app)
    # Invalid PNIP (bad hash + wrong policy pack id) should 400
    r = client.post(
        "/v1/ledger/record-input",
        json={"case_id": "CASE-1", "document_hash": "sha1:bad"},
        headers={"X-Policy-Pack-ID": "WRONG", "X-Jurisdiction": "PL:lex"},
    )
    assert r.status_code == 400
    body = r.json()
    assert body.get("detail", {}).get("error", {}).get("code") == "PNIP_INVALID"
