#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/uri.py                                      |
# | ROLE: Project module.                                       |
# | PLIK: core/pfs/uri.py                                      |
# | ROLA: Moduł projektu.                                       |
# +-------------------------------------------------------------+

"""

PL: Pomocnicze funkcje do budowania URI ProofFS (pfs://...).
    Obecnie obsługiwane są odnośniki do załączników e‑maili
    w postaci `pfs://mail/<mail_id>/<filename>`.

EN: Helper functions for building ProofFS URIs (pfs://...).
    Currently supports e‑mail attachment references in the form
    `pfs://mail/<mail_id>/<filename>`.

"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import re

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


_SAFE_RE = re.compile(r"[^A-Za-z0-9._-]+")


def _sanitize(s: str) -> str:
    """
    PL/EN: Replace disallowed characters with '-', keep alnum, dot, underscore and dash.
    """
    s = s.strip()
    s = s.replace(" ", "-")
    return _SAFE_RE.sub("-", s)


def mail_attachment_uri(mail_id: str, filename: str) -> str:
    """
    PL: Zwraca URI ProofFS dla załącznika e‑maila.
    EN: Returns ProofFS URI for an e‑mail attachment.
    """
    mid = _sanitize(mail_id or "mail")
    fname = _sanitize(filename or "file")
    return f"pfs://mail/{mid}/{fname}"


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
