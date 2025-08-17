# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/services/test_exporter_provenance.py|
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


"""
PL: Testy jednostkowe / integracyjne modułu.
EN: Module test suite (unit/integration).
"""

# +-------------------------------------------------------------+
# | CERTEUS - Tests: Exporter & Ledger                          |
# +-------------------------------------------------------------+
from pathlib import Path

from services.exporter_service import export_answer_to_txt
from services.ledger_service.ledger import (
    compute_provenance_hash,
    verify_provenance_hash,
)


def test_export_and_hash(tmp_path: Path):
    answer = {
        "case_id": "pl-001",
        "title": "T",
        "thesis": "X",
        "reasoning": "Y",
        "status": "ok",
        "confidence": 0.9,
    }
    out = tmp_path / "out.txt"
    path = export_answer_to_txt(answer, out_path=str(out), create_ledger_entry=False)
    assert Path(path).exists()

    h = compute_provenance_hash(answer, include_timestamp=False)
    assert verify_provenance_hash(answer, h)
