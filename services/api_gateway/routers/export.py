#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: services/api_gateway/routers/export.py              |

# | ROLE: Project module.                                       |

# | PLIK: services/api_gateway/routers/export.py              |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

"""

PL: Endpoint eksportu. Przyjmuje `case_id` i `analysis_result`, zapisuje raport

    tekstowy do katalogu `exports/`, po czym zwraca ścieżkę oraz provenance

    zawierające hash SHA-256 pliku raportu, znacznik czasu UTC i listę artefaktów.

EN: Export endpoint. Accepts `case_id` and `analysis_result`, writes a text

    report under `exports/`, then returns the path and provenance with the

    report file's SHA-256, UTC timestamp, and artifacts list.

"""

from __future__ import annotations

from collections.abc import Mapping
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
from typing import Any

from fastapi import APIRouter, HTTPException, Response
from pydantic import BaseModel, Field

router = APIRouter(prefix="", tags=["export"])

# === MODELS / MODELE ===


class ExportPayload(BaseModel):
    case_id: str = Field(..., description="Public case id, e.g. 'pl-286kk-0001'")

    analysis_result: Mapping[str, Any] = Field(default_factory=dict)

    fmt: str = Field(
        "report",
        description="Output format: report|file|docx|json (default: report)",
    )

    write_ledger: bool = Field(default=False, description="If true, record provenance hash in Ledger")


class ExportResponse(BaseModel):
    path: str

    message: str

    provenance: dict[str, Any] | None = None  # optional to keep tests happy


# === HELPERS ===


def _hash_file_sha256(path: Path) -> str:
    h = hashlib.sha256()

    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)

    return h.hexdigest()


def _now_iso_utc() -> str:
    return datetime.now(UTC).isoformat()


def _write_report(case_id: str, analysis_result: Mapping[str, Any], out_dir: Path) -> Path:
    """

    PL: Zapis raportu jako .txt z podstawowym podsumowaniem i pretty JSON.

    EN: Write .txt report with a tiny header + pretty JSON of the analysis.

    """

    out_dir.mkdir(parents=True, exist_ok=True)

    filename = f"raport_{case_id}.txt"

    path = out_dir / filename

    lines: list[str] = []

    lines.append("# CERTEUS – Raport analityczny / Analytical Report")

    lines.append(f"Case: {case_id}")

    try:
        pretty = json.dumps(analysis_result, ensure_ascii=False, indent=2, sort_keys=True)

    except Exception:
        pretty = str(analysis_result)

    lines.append("")

    lines.append("=== ANALIZA / ANALYSIS ===")

    lines.append(pretty)

    path.write_text("\n".join(lines), encoding="utf-8")

    return path


# === ENDPOINT ===


@router.post("/v1/export", response_model=ExportResponse)
def export_endpoint(payload: ExportPayload, response: Response) -> ExportResponse:
    """

    PL: Generuje raport i zwraca ścieżkę + provenance (hash, timestamp, artifacts).

    EN: Generate report and return path + provenance (hash, timestamp, artifacts).

    """

    case_id = payload.case_id.strip()

    if not case_id:
        raise HTTPException(status_code=400, detail="case_id required")

    out_dir = Path("exports")

    export_path: Path | None = None
    if payload.fmt == "report":
        export_path = _write_report(case_id, payload.analysis_result, out_dir)
    elif payload.fmt == "file":
        export_path = out_dir / f"{case_id}.json"
        out_dir.mkdir(parents=True, exist_ok=True)
        export_path.write_text(
            json.dumps(payload.analysis_result, ensure_ascii=False, indent=2, sort_keys=True),
            encoding="utf-8",
        )
    elif payload.fmt == "docx":
        export_path = out_dir / f"{case_id}.docx"
        out_dir.mkdir(parents=True, exist_ok=True)
        export_path.write_text(
            json.dumps(payload.analysis_result, ensure_ascii=False, indent=2, sort_keys=True),
            encoding="utf-8",
        )
    elif payload.fmt == "json":
        # No file on disk; we still compute provenance on JSON content
        export_path = None
    else:
        raise HTTPException(status_code=400, detail=f"Unsupported fmt: {payload.fmt}")

    # Build provenance / Budowa provenance

    timestamp = _now_iso_utc()
    if export_path and export_path.exists():
        h = _hash_file_sha256(export_path)
        artifacts = {"report": str(export_path)} if payload.fmt == "report" else {"artifact": str(export_path)}
    else:
        # Hash JSON content when no file was created
        try:
            content = json.dumps(payload.analysis_result, ensure_ascii=False, sort_keys=True)
        except Exception:
            content = str(payload.analysis_result)
        h = hashlib.sha256(content.encode("utf-8")).hexdigest()
        artifacts = {}

    prov: dict[str, Any] = {
        "hash_sha256": h,
        "timestamp_utc": timestamp,
        "artifacts": artifacts,
    }

    # Optional ledger record
    if payload.write_ledger:
        try:
            from services.ledger_service.ledger import compute_provenance_hash, ledger_service

            # Ledger hash over analysis summary + export info
            ledger_doc = {
                "export": {
                    "case": case_id,
                    "fmt": payload.fmt,
                    "hash": h,
                    "timestamp": timestamp,
                }
            }
            doc_hash = "sha256:" + compute_provenance_hash(ledger_doc, include_timestamp=False)
            ledger_service.record_input(case_id=case_id, document_hash=doc_hash)
        except Exception:
            # Non-fatal for export
            pass

    # PCO headers (export provenance)
    try:
        response.headers["X-CERTEUS-PCO-export.hash"] = h
        response.headers["X-CERTEUS-PCO-export.timestamp"] = timestamp
        if export_path:
            response.headers["X-CERTEUS-PCO-export.path"] = str(export_path)
    except Exception:
        pass

    return ExportResponse(
        path=str(export_path) if export_path else "",
        message=(
            f"Report generated at {export_path}"
            if payload.fmt == "report"
            else (f"Artifact written to {export_path}" if export_path else "JSON returned")
        ),
        provenance=prov,
    )
