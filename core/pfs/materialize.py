#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/materialize.py                              |
# | ROLE: Project module.                                       |
# | PLIK: core/pfs/materialize.py                              |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Materializacja artefaktów ProofFS (read-only tree) — stub do testów/dev.
EN: Materialize ProofFS artifacts (read-only tree) — dev/test stub.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
from pathlib import Path
import time
from typing import Any

from .uri import _sanitize
from .resolve import resolve_uri


def _root_dir() -> Path:
    return Path(os.getenv("PROOFS_FS_ROOT") or "data/proof_fs").resolve()


def materialize_mail_attachment(mail_id: str, filename: str, meta: dict[str, Any] | None = None) -> Path:
    """
    PL: Tworzy stub pliku pod data/proof_fs/mail/<mail_id>/<filename> z JSON‑em metadanych.
    EN: Creates a stub file under data/proof_fs/mail/<mail_id>/<filename> with JSON metadata.
    """
    mid = _sanitize(mail_id or "mail")
    fname = _sanitize(filename or "file")
    root = _root_dir() / "mail" / mid
    root.mkdir(parents=True, exist_ok=True)
    p = root / fname
    payload = {
        "_kind": "mail.attachment",
        "mail_id": mail_id,
        "filename": filename,
        "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        **(meta or {}),
    }
    # Idempotent write (overwrite ok for stub)
    p.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return p


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===


def materialize_uri(uri: str, meta: dict[str, Any] | None = None) -> Path:
    """
    PL/EN: Materialize artifact for a given pfs:// URI.
    Currently supports mail attachments: pfs://mail/<mail_id>/<filename>
    """
    res = resolve_uri(uri)
    parts = res.path.parts
    # Expect .../mail/<mail_id>/<filename>
    try:
        idx = parts.index("mail")
        mail_id = parts[idx + 1]
        filename = parts[idx + 2]
    except Exception as _e:  # pragma: no cover - defensive
        raise ValueError("unsupported ProofFS URI for materialize") from _e
    return materialize_mail_attachment(mail_id, filename, meta)
