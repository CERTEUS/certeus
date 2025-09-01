#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/exporter_service/exporter.py               |

# | ROLE: Project module.                                       |

# | PLIK: services/exporter_service/exporter.py               |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +=====================================================================+

# |                          CERTEUS                                    |

# +=====================================================================+

# | MODULE:  F:/projekty/certeus/services/exporter_service/exporter.py   |

# | DATE:    2025-08-17                                                  |

# +=====================================================================+


"""

PL: Eksport raportów i artefaktów procesu.

EN: Report/artefact exporter.

"""

from __future__ import annotations

from collections.abc import Mapping
import json
from pathlib import Path
from typing import Any

# (hash helpers są w ledger_service, ale nie są tu potrzebne do samego eksportu)


TEMPL_REPORT = """# CERTEUS Report

Case: {case_id}

Status: {status}

Model: {model}

"""


class ExporterService:
    def __init__(self, template_dir: str, output_dir: str) -> None:
        self.template_dir = Path(template_dir)

        self.output_dir = Path(output_dir)

        self.output_dir.mkdir(parents=True, exist_ok=True)

    def export_report(self, case_id: str, analysis: dict[str, Any]) -> Path:
        status = str(analysis.get("status", "")).upper()

        model = analysis.get("model", "")

        content = TEMPL_REPORT.format(case_id=case_id, status=status, model=model)

        out = self.output_dir / f"{case_id}.txt"

        out.write_text(content, encoding="utf-8")

        return out


def export_answer_to_txt(answer: Mapping[str, Any], *, out_path: str, create_ledger_entry: bool = False) -> str:
    p = Path(out_path)

    p.parent.mkdir(parents=True, exist_ok=True)

    p.write_text(json.dumps(answer, indent=2, sort_keys=True), encoding="utf-8")

    return str(p)


def export_answer(answer: Mapping[str, Any], *, fmt: str, output_dir: Path | None = None):
    """

    - fmt="json": return pretty json string

    - fmt="file": write <case_id>.json to output_dir, return Path

    - fmt="docx": write placeholder .docx (text), return Path

    """

    if fmt == "json":
        return json.dumps(answer, indent=2, sort_keys=True)

    outdir = output_dir or Path("build/exports")

    outdir.mkdir(parents=True, exist_ok=True)

    case_id = str(answer.get("case_id", "case"))

    if fmt == "file":
        p = outdir / f"{case_id}.json"

        p.write_text(json.dumps(answer, indent=2, sort_keys=True), encoding="utf-8")

        return p

    if fmt == "docx":
        p = outdir / f"{case_id}.docx"

        p.write_text(json.dumps(answer, indent=2, sort_keys=True), encoding="utf-8")

        return p

    raise ValueError(f"Unsupported fmt: {fmt}")
