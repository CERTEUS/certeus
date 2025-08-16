# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |      Core Engine for Reliable & Unified Systems             |
# +-------------------------------------------------------------+
# | FILE: services/sipp_indexer_service/index_isap.py           |
# | ROLE: Index ISAP (stub): fetch mock act and write snapshot  |
# |       JSON to packs/jurisdictions/PL/isap_data/.            |
# +-------------------------------------------------------------+

"""
PL: Indeksuje (stub) akt prawny z ISAP: pobiera migawkę przez IsapAdapter
    i zapisuje JSON z metadanymi do katalogu danych. Bezpieczne dla testów:
    funkcje przyjmują katalog wyjściowy (domyślny w repo).
EN: Indexes (stub) a legal act from ISAP: fetches a snapshot via IsapAdapter
    and writes JSON with metadata to the data directory. Test-friendly: functions
    accept an output dir (repo default provided).
"""

from __future__ import annotations

import json
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Optional
from pydantic import TypeAdapter

from services.sipp_indexer_service.isap_adapter import IsapAdapter
from services.sipp_indexer_service.models import LegalActSnapshot


def _repo_default_data_dir() -> Path:
    """
    PL: Domyślny katalog danych w repo.
    EN: Repository default data directory.
    """
    return Path("packs") / "jurisdictions" / "PL" / "isap_data"


def _snapshot_filename(act_id: str, version_id: str, snapshot_ts: datetime) -> str:
    """
    PL: Buduje deterministyczną nazwę pliku: {act_id}__{version_id}__{ts}.json
    EN: Builds a deterministic filename: {act_id}__{version_id}__{ts}.json
    """
    safe_ts = snapshot_ts.replace(tzinfo=timezone.utc).isoformat().replace(":", "-")
    return f"{act_id}__{version_id}__{safe_ts}.json"


def index_act(
    act_id: str,
    out_dir: Optional[Path] = None,
    at: Optional[date] = None,
    adapter: Optional[IsapAdapter] = None,
) -> Path:
    """
    PL: Pobiera migawkę aktu i zapisuje ją jako JSON do katalogu danych.
    EN: Fetches an act snapshot and writes it as JSON to the data directory.
    """
    adapter = adapter or IsapAdapter()
    out_dir = out_dir or _repo_default_data_dir()
    out_dir.mkdir(parents=True, exist_ok=True)

    snap: LegalActSnapshot = adapter.fetch_act_snapshot(act_id, at=at)

    # Pydantic v2: deterministyczny dump do Python dict z trybem JSON
    payload = TypeAdapter(LegalActSnapshot).dump_python(snap, mode="json")

    # Wzbogacamy o metadane techniczne (UTC ISO)
    payload["_certeus"] = {
        "act_id": snap.act_id,
        "version_id": snap.version_id,
        "snapshot_timestamp_utc": snap.snapshot_timestamp.replace(
            tzinfo=timezone.utc
        ).isoformat(),
    }

    out_path = out_dir / _snapshot_filename(
        act_id=snap.act_id,
        version_id=snap.version_id,
        snapshot_ts=snap.snapshot_timestamp,
    )
    with out_path.open("w", encoding="utf-8", newline="\n") as f:
        json.dump(payload, f, ensure_ascii=False)

    return out_path
