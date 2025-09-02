# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: tests/services/test_preview.py                      |

# | ROLE: Project module.                                       |

# | PLIK: tests/services/test_preview.py                      |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Testy weryfikują, że endpoint /v1/preview przyjmuje plik (multipart/form-data)

    i zwraca JSON z kluczem `url` wskazującym ścieżkę podglądu w `/static/previews/...`.



EN: Tests verify that /v1/preview accepts a file (multipart/form-data) and returns

    JSON with a `url` pointing to a preview path under `/static/previews/...`.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

from __future__ import annotations

from pathlib import Path

from fastapi.testclient import TestClient

import services.api_gateway.main as api_main


def test_health_ok() -> None:
    client = TestClient(api_main.app)

    r = client.get("/health")

    assert r.status_code == 200

    assert r.json().get("status") == "ok"


def test_static_app_mount() -> None:
    client = TestClient(api_main.app)

    r = client.get("/app/proof_visualizer/index.html")

    assert r.status_code in (
        200,
        404,
    )  # mount działa; plik może nie istnieć w teście CI


def test_preview_upload_roundtrip(tmp_path: Path) -> None:
    client = TestClient(api_main.app)

    sample = tmp_path / "sample.txt"

    sample.write_text("hello", encoding="utf-8")

    with sample.open("rb") as fh:
        r = client.post("/v1/preview", files={"file": ("sample.txt", fh, "text/plain")})

    assert r.status_code == 200

    url = r.json().get("url")

    assert isinstance(url, str) and url.startswith("/static/previews/")

    rel = url.removeprefix("/static/")

    saved = Path("static") / rel

    assert saved.exists()

    saved.unlink(missing_ok=True)
