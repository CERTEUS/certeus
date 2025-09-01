# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/preview.py             |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/preview.py             |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""PL: Router podglądu plików. EN: Preview router."""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from pathlib import Path
import shutil
from typing import Annotated
import uuid

from fastapi import APIRouter, File, UploadFile
from fastapi.responses import JSONResponse

# === KONFIGURACJA / CONFIGURATION ===
STATIC_PREV = Path("static/previews")

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


router = APIRouter()


STATIC_PREV.mkdir(parents=True, exist_ok=True)


@router.post("/v1/preview")
async def preview(file: Annotated[UploadFile, File(...)]) -> JSONResponse:
    """

    PL: Zwraca URL do podglądu pliku. Na razie zapisuje pod /static/previews/.

    EN: Returns a URL for preview. For now writes into /static/previews/.

    """

    raw_name: str = file.filename or "upload.bin"  # UploadFile.filename can be None

    ext = Path(raw_name).suffix.lower()

    safe_name = f"{uuid.uuid4().hex}{ext}"

    dst = STATIC_PREV / safe_name

    try:
        with dst.open("wb") as out:
            shutil.copyfileobj(file.file, out)

    finally:
        await file.close()

    return JSONResponse({"url": f"/static/previews/{safe_name}"})


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
