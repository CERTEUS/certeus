# +-------------------------------------------------------------+
# |                 CERTEUS - Exporter Service (MVP)            |
# +-------------------------------------------------------------+
# | FILE/PLIK: services/exporter_service/exporter.py            |
# | ROLE/ROLA: Generuje raporty na bazie szablonów.             |
# +-------------------------------------------------------------+
"""
PL: Serwis eksportu raportów. Wypełnia szablon danymi analizy i zapisuje .txt.
EN: Report export service. Fills a template with analysis data and writes .txt.
"""

from __future__ import annotations
from pathlib import Path
from typing import Any, Dict
from datetime import datetime, timezone


class ExporterService:
    """PL: Serwis eksportu raportów. EN: Report exporting service."""

    def __init__(
        self, template_dir: str = "templates", output_dir: str = "out"
    ) -> None:
        self.template_dir = Path(template_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True, parents=True)
        print("INFO: ExporterService initialized.")

    def export_report(self, case_id: str, analysis_data: Dict[str, Any]) -> Path:
        """PL: Generuje raport tekstowy z szablonu. EN: Generate text report."""
        print(f"INFO: Generating report for case: {case_id}")
        template_path = self.template_dir / "answer_contract.txt.placeholder"
        template_content = template_path.read_text(encoding="utf-8")

        report_data: Dict[str, Any] = {
            "CASE_ID": case_id,
            "ANALYSIS_DATE": datetime.now(timezone.utc).strftime(
                "%Y-%m-%d %H:%M:%S UTC"
            ),
            "THESIS": f"Analiza zgodności z art. 286 k.k. dla sprawy {case_id}",
            "VERIFICATION_STATUS": str(analysis_data.get("status", "N/A")).upper(),
            "SOLUTION_MODEL": analysis_data.get("model", "Brak modelu."),
            "PROVENANCE_HASH": "sha256:coming_soon...",
        }

        report_content = template_content
        for key, value in report_data.items():
            report_content = report_content.replace(f"${{{key}}}", str(value))

        output_path = self.output_dir / f"raport_{case_id}.txt"
        output_path.write_text(report_content, encoding="utf-8")
        print(f"✅ Report generated successfully: {output_path}")
        return output_path
