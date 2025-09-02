# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/e2e/test_e2e_export_endpoint.py               |

# | ROLE: Project module.                                       |

# | PLIK: tests/e2e/test_e2e_export_endpoint.py               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Test E2E endpointu /v1/export – oczekuje ścieżki do wygenerowanego raportu.

EN: E2E test for /v1/export endpoint – expects path to generated report.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

# [BLOCK: IMPORTS]

from __future__ import annotations

from pathlib import Path
from typing import Any, TypedDict

from fastapi.testclient import TestClient

from services.api_gateway.main import app

# [BLOCK: TYPES]


class ExportPayload(TypedDict):
    """PL: Struktura żądania dla /v1/export.

    EN: Request shape for /v1/export."""

    case_id: str

    analysis_result: dict[str, Any]


# [BLOCK: CLIENT]

client = TestClient(app)

# +-------------------------------------------------------------+

# | TEST: /v1/export returns generated report path              |

# +-------------------------------------------------------------+


def test_export_endpoint_returns_path() -> None:
    # [BLOCK: ARRANGE]

    payload: ExportPayload = {
        "case_id": "pl-286kk-0001",
        "analysis_result": {"status": "sat", "model": "[x=True]"},
    }

    # [BLOCK: ACT]

    response = client.post("/v1/export", json=payload)

    # [BLOCK: ASSERT]

    assert response.status_code == 200

    body: dict[str, Any] = response.json()

    # podstawowe oczekiwania

    assert "path" in body and isinstance(body["path"], str)

    assert "message" in body and isinstance(body["message"], str)

    assert body["message"].lower().startswith("report generated")

    # konwencja nazwy pliku (zgodna z ExporterService)

    assert Path(body["path"]).name == f"raport_{payload['case_id']}.txt"
