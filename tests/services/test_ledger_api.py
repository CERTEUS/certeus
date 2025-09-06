#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_ledger_api.py                   |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_ledger_api.py                   |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

from __future__ import annotations

from hashlib import sha256

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_ledger_record_and_prove() -> None:
    case_id = "case-ledger-01"

    doc_hash = "sha256:" + sha256(b"doc").hexdigest()

    r = client.post(
        "/v1/ledger/record-input", json={"case_id": case_id, "document_hash": doc_hash}
    )

    assert r.status_code == 200, r.text

    body = r.json()

    assert body["case_id"] == case_id

    assert body["document_hash"] == doc_hash

    r2 = client.get(f"/v1/ledger/{case_id}/records")

    assert r2.status_code == 200

    items = r2.json()

    assert any(it["chain_self"] == body["chain_self"] for it in items)

    r3 = client.get(f"/v1/ledger/{case_id}/prove")

    assert r3.status_code == 200

    receipt = r3.json()

    assert receipt["case_id"] == case_id

    assert receipt["count"] >= 1
