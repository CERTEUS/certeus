#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/sipp_indexer_service/index_isap.py         |

# | ROLE: Project module.                                       |

# | PLIK: services/sipp_indexer_service/index_isap.py         |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


"""

PL: Generator migawek ISAP. Buduje pojedynczy plik JSON `<act_id>.json`

    z polami `snapshot_timestamp` i `_certeus.snapshot_timestamp_utc`.

EN: ISAP snapshot generator. Produces a single JSON `<act_id>.json` with

    `snapshot_timestamp` and `_certeus.snapshot_timestamp_utc` fields.

"""
# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === MODELE / MODELS ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===


#!/usr/bin/env python3

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from datetime import UTC, datetime
from hashlib import sha256
import json
from pathlib import Path
from typing import Any


@dataclass
class ActSnapshot:
    act_id: str

    version_id: str

    text_sha256: str

    source_url: str

    title: str | None

    text: str

    snapshot_timestamp: str

    at: str | None = None

    _certeus: dict[str, Any] = field(default_factory=dict)


def _snapshot_for(act_id: str) -> ActSnapshot:
    text = (
        "Art. 286 k.k.: Kto, w celu osiągnięcia korzyści majątkowej, "
        "doprowadza inną osobę do niekorzystnego rozporządzenia mieniem "
        "za pomocą wprowadzenia w błąd..."
    )

    digest = "sha256:" + sha256(text.encode("utf-8")).hexdigest()

    now = datetime.now(UTC).isoformat(timespec="seconds")

    return ActSnapshot(
        act_id=act_id,
        version_id="2023-10-01",
        text_sha256=digest,
        source_url="https://isap.sejm.gov.pl/isap.nsf/DocDetails.xsp?id=WDU19970880553",
        title="Kodeks karny – art. 286",
        text=text,
        snapshot_timestamp=now,
        at=None,
        _certeus={"snapshot_timestamp_utc": now},
    )


def index_act(act_id: str, out_dir: Path | None = None) -> Path:
    """Create a single JSON snapshot file and return its path."""

    snap = _snapshot_for(act_id)

    out_dir = Path(out_dir or Path("snapshots"))

    out_dir.mkdir(parents=True, exist_ok=True)

    path = out_dir / f"{act_id}.json"

    path.write_text(json.dumps(asdict(snap), ensure_ascii=False, indent=2), encoding="utf-8")

    return path
