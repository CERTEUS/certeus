# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |      Core Engine for Reliable & Unified Systems             |
# +-------------------------------------------------------------+
# | FILE: services/sipp_indexer_service/isap_adapter.py         |
# | ROLE: Stub adapter for ISAP. Creates LegalActSnapshot.      |
# +-------------------------------------------------------------+

"""
PL: Stub adaptera do ISAP. Wersja MVP: zwraca stałą migawkę dla
    podanego act_id, z poprawnym SHA256 i timestampem UTC.
EN: ISAP adapter stub. MVP version: returns a constant snapshot
    for a given act_id with proper SHA256 and UTC timestamp.
"""

from __future__ import annotations

import hashlib
from datetime import date, datetime, timezone
from typing import Optional

from .models import LegalActSnapshot


def _ascii_info(msg: str) -> None:
    try:
        from utils.console import info as _info  # type: ignore

        s = msg.encode("ascii", "ignore").decode("ascii")
        _info(s)
    except Exception:
        s = msg.encode("ascii", "ignore").decode("ascii")
        print(f"[INFO] {s}")


class IsapAdapter:
    """
    PL: Symuluje pobranie aktu prawnego i tworzy migawkę.
    EN: Simulates fetching a legal act and creating its snapshot.
    """

    def fetch_act_snapshot(
        self, act_id: str, at: Optional[date] = None
    ) -> LegalActSnapshot:
        """
        PL: Zwraca LegalActSnapshot dla zadanego act_id. Parametr 'at' to
            data, na ktora prosimy o stan prawa (stub ignoruje).
        EN: Returns LegalActSnapshot for given act_id. 'at' asks for state
            at given date (ignored by stub).
        """
        _ascii_info(f"ISAP Stub fetching act_id={act_id} at={at}")

        mock_text = (
            "Art. 286. § 1. Kto, w celu osiagniecia korzysci majatkowej, doprowadza "
            "inna osobe do niekorzystnego rozporzadzenia mieniem za pomoca wprowadzenia "
            "jej w blad albo wyzyskania bledu lub niezdolnosci do nalezytego pojmowania "
            "przedsiewzietego dzialania, podlega karze pozbawienia wolnosci od 6 miesiecy do lat 8."
        )
        text_hash = f"sha256:{hashlib.sha256(mock_text.encode('utf-8')).hexdigest()}"

        snapshot = LegalActSnapshot(
            act_id=act_id,
            version_id="2023-10-01",
            text_sha256=text_hash,
            source_url="https://isap.sejm.gov.pl/isap.nsf/DocDetails.xsp?id=WDU19970880553",
            valid_from=date(2023, 10, 1),
            snapshot_timestamp=datetime.now(timezone.utc),
        )
        return snapshot
