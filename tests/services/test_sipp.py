# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_sipp.py                         |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_sipp.py                         |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Testuje endpoint /v1/sipp/snapshot/{act_id}.

EN: Tests the /v1/sipp/snapshot/{act_id} endpoint.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from __future__ import annotations

import json
from pathlib import Path

from fastapi.testclient import TestClient

from services.api_gateway.main import app

client = TestClient(app)


def test_get_snapshot_endpoint_success() -> None:
    act_id = "kk-art-286"

    resp = client.get(f"/v1/sipp/snapshot/{act_id}")

    assert resp.status_code == 200

    data = resp.json()

    assert data["act_id"] == act_id

    assert data["version_id"] == "2023-10-01"

    assert data["source_url"]

    assert data["text_sha256"].startswith("sha256:")

    assert "snapshot_timestamp" in data


def test_get_snapshot_with_at_param() -> None:
    act_id = "kk-art-286"

    resp = client.get(f"/v1/sipp/snapshot/{act_id}?at=2024-11-24")

    assert resp.status_code == 200

    data = resp.json()

    assert data["act_id"] == act_id

    # Stub ignores 'at', but API must accept the param gracefully.

    assert data["version_id"] == "2023-10-01"


def test_index_isap_writes_snapshot_file(tmp_path: Path) -> None:
    from services.sipp_indexer_service.index_isap import index_act

    p = index_act("kk-art-286", out_dir=tmp_path)  # nie piszemy do repo podczas testu

    assert p.exists()

    data = json.loads(p.read_text(encoding="utf-8"))

    assert data["act_id"] == "kk-art-286"

    assert data["text_sha256"].startswith("sha256:")

    assert "snapshot_timestamp" in data

    assert "_certeus" in data and "snapshot_timestamp_utc" in data["_certeus"]
