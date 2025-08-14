# tests/services/test_exporter.py
from __future__ import annotations

from pathlib import Path
from services.exporter_service.exporter import export_answer


def test_exporter_creates_files(tmp_path: Path) -> None:
    # Jeśli export_answer nie akceptuje Path, użyj: str(tmp_path)
    export_answer("pl-286kk-0001", out_dir=tmp_path)

    docx: Path = tmp_path / "pl-286kk-0001.docx"
    pdf: Path = tmp_path / "pl-286kk-0001.pdf"

    assert docx.exists()
    assert pdf.exists()
