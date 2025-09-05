#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/xattrs.py                                   |
# | ROLE: ProofFS xattrs (PNIP/PCO) read-only API               |
# | PLIK: core/pfs/xattrs.py                                   |
# | ROLA: Atrybuty rozszerzone ProofFS (PNIP/PCO) — tylko odczyt|
# +-------------------------------------------------------------+

"""
PL: Odczyt atrybutów rozszerzonych (xattrs) dla artefaktów ProofFS.
    Wersja stub (CI‑friendly): PNIP liczony jako sha256 z pliku;
    PCO syntetyczny na podstawie PNIP (bez kluczy prywatnych).

EN: Read extended attributes (xattrs) for ProofFS artifacts.
    CI‑friendly stub: PNIP computed as file sha256; PCO synthesized
    from PNIP (no private keys required).
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
from pathlib import Path
from typing import Any

from .resolve import resolve_uri

try:  # optional import; keep loose coupling in CI
    from core.pco.public_payload import PublicPCO  # type: ignore
except Exception:  # pragma: no cover - fallback lightweight struct
    PublicPCO = None  # type: ignore


def _sha256_hex_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


def _load_sidecar(p: Path) -> dict[str, Any] | None:
    """
    PL/EN: Load optional sidecar xattrs JSON if present: <file>.xattrs.json
    """
    sidecar = p.with_suffix(p.suffix + ".xattrs.json")
    try:
        if sidecar.exists():
            raw = json.loads(sidecar.read_text(encoding='utf-8'))
            if isinstance(raw, dict):
                return raw
    except Exception:
        pass
    return None


def _synthesize_pco(*, rid: str, pnip_hex: str) -> dict[str, Any]:
    """
    PL: Zwraca minimalny publiczny PCO zgodny strukturalnie, ale niesygnowany
        (wystarczający do inspekcji i bramek spójności PNIP/PCO w CI).

    EN: Return a minimal public PCO, structurally valid but unsigned
        (enough for inspection and PNIP/PCO gates in CI).
    """
    payload = {
        "rid": rid,
        "smt2_hash": pnip_hex.lower(),
        "lfsc": "(set-logic QF_BV) ; stub",
        "merkle_proof": [],
        "signature": "",
        "issued_at": None,
        "drat": None,
    }
    # If PublicPCO dataclass is available, create instance and convert to dict
    if PublicPCO is not None:
        try:
            pc = PublicPCO(
                rid=payload["rid"],
                smt2_hash=payload["smt2_hash"],
                lfsc=payload["lfsc"],
                merkle_proof=[],
                signature="",
                issued_at=None,
                drat=None,
            )
            return asdict(pc)
        except Exception:
            pass
    return payload


def get_xattrs_for_path(p: Path) -> dict[str, Any]:
    """
    PL/EN: Return xattrs for a filesystem path.
    Priority:
      1) Sidecar JSON (<file>.xattrs.json) if present
      2) Synthesize PNIP/PCO based on file content and pathname
    """
    x: dict[str, Any] | None = _load_sidecar(p)
    if not x:
        # compute PNIP from file content
        pnip_hex = _sha256_hex_path(p)
        # rid heuristic: last two path parts (e.g., mail/<MAIL_ID>/<FILENAME>)
        parts = p.parts
        rid = "/".join(parts[-2:]) if len(parts) >= 2 else p.name
        x = {
            "pnip": f"sha256:{pnip_hex}",
            "pco": _synthesize_pco(rid=rid, pnip_hex=pnip_hex),
        }
    # Ensure basic normalization
    if isinstance(x.get("pnip"), str) and x["pnip"].startswith("sha256:"):
        pass
    elif isinstance(x.get("pnip"), str):
        x["pnip"] = f"sha256:{x['pnip']}"
    return x  # type: ignore[return-value]


def get_xattrs_for_uri(uri: str) -> dict[str, Any]:
    """
    PL/EN: Resolve a pfs:// URI and fetch xattrs.
    Raises ValueError if URI invalid or file does not exist.
    """
    res = resolve_uri(uri)
    if not res.exists:
        raise FileNotFoundError(f"artifact not found: {uri}")
    return get_xattrs_for_path(res.path)
