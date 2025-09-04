#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/resolve.py                                  |
# | ROLE: Project module.                                       |
# | PLIK: core/pfs/resolve.py                                  |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""
PL: Rozwiązywanie URI ProofFS (pfs://...) do ścieżek w drzewie RO.
EN: Resolve ProofFS URIs (pfs://...) into paths within the RO tree.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path

from .uri import _sanitize

# === MODELE / MODELS ===


@dataclass
class ResolveResult:
    uri: str
    path: Path
    exists: bool
    size: int | None = None


# === LOGIKA / LOGIC ===


def _root_dir() -> Path:
    return Path(os.getenv("PROOFS_FS_ROOT") or "data/proof_fs").resolve()


def resolve_uri(uri: str, root: Path | None = None) -> ResolveResult:
    if not isinstance(uri, str) or not uri.startswith("pfs://"):
        raise ValueError("invalid ProofFS URI")
    rest = uri[len("pfs://") :]
    parts = [p for p in rest.split("/") if p]
    if not parts:
        raise ValueError("invalid ProofFS URI path")
    # sanitize each segment to avoid path traversal
    safe_parts = [_sanitize(seg) for seg in parts]
    base = root or _root_dir()
    file_path = base.joinpath(*safe_parts)
    exists = file_path.exists() and file_path.is_file()
    size: int | None = file_path.stat().st_size if exists else None
    return ResolveResult(uri=uri, path=file_path, exists=exists, size=size)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
