# +=====================================================================+
# |                          CERTEUS                                    |
# +=====================================================================+
# | MODULE:  F:/projekty/certeus/tests/services/test_exporter.py         |
# | DATE:    2025-08-17                                                  |
# +=====================================================================+


# +-------------------------------------------------------------+
# |               CERTEUS - Exporter Service Tests              |
# +-------------------------------------------------------------+
# | FILE: tests/services/test_exporter.py                       |
# +-------------------------------------------------------------+
"""
PL: Testy serwisu ExporterService – sprawdza poprawność wypełnienia szablonu.
EN: Tests for ExporterService – verifies template population correctness.
"""

from __future__ import annotations

from pathlib import Path
import tempfile

from services.exporter_service import ExporterService


def test_export_report_creates_file_with_replaced_content():
    with tempfile.TemporaryDirectory() as tmpdir:
        outdir = Path(tmpdir) / "out"
        service = ExporterService(template_dir="templates", output_dir=str(outdir))
        case_id = "test-export-007"
        analysis = {"status": "sat", "model": "[a=True,b=False]"}

        report_path = service.export_report(case_id, analysis)

        assert report_path.exists()
        content = report_path.read_text(encoding="utf-8")
        assert case_id in content
        assert "SAT" in content
        assert "[a=True,b=False]" in content
