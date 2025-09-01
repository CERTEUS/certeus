#!/usr/bin/env python3
# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/make_merkle_sample.py                       |

# | ROLE: Project module.                                       |

# | PLIK: scripts/make_merkle_sample.py                       |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


# +======================================================================+

# |                               CERTEUS                                |

# +======================================================================+

# | FILE / PLIK: scripts/make_merkle_sample.py                           |

# | ROLE / ROLA:                                                          |

# |  EN: Build demo public bundle (non-empty Merkle path) and sign it.   |

# |  PL: Buduje przykładowy publiczny bundle (niepusta ścieżka Merkle)   |

# |      i podpisuje go.                                                 |

# +======================================================================+

# Założenia:

# - czyta klucz prywatny Ed25519 z PEM: ED25519_PRIVKEY_PEM

# - zapisuje do $PROOF_BUNDLE_DIR (fallback: ./data/public_pco)

# - materiał demo: LFSC/SMT2 w razie braku plików podawanych flagami

# ----Bloki----- IMPORTY (PEP 8/PEP 585)

#   - max 120 znaków/linia

"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from argparse import ArgumentParser

import base64

from collections.abc import Iterable

import hashlib

import json

import os

from pathlib import Path

import sys

from typing import Any, TypedDict

from cryptography.hazmat.primitives import serialization

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===
class MerkleStep(TypedDict):
    sibling: str  # hex

    dir: str  # 'L' | 'R'

# === LOGIKA / LOGIC ===

























DEFAULT_DIR = os.getenv("PROOF_BUNDLE_DIR", "./data/public_pco")


#!/usr/bin/env python3


# ----Bloki----- TYPY


# ----Bloki----- POMOCNICZE


def _hx_text(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def _is_hex64(x: str) -> bool:
    return isinstance(x, str) and len(x) == 64 and all(c in "0123456789abcdef" for c in x.lower())


def sha256_hex_utf8(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def compute_bundle_hash_hex(pub: dict[str, Any]) -> str:
    payload = {"smt2_hash": pub["smt2_hash"], "lfsc_sha256": sha256_hex_utf8(pub["lfsc"])}

    if pub.get("drat") is not None:
        payload["drat_sha256"] = sha256_hex_utf8(pub["drat"])

    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")

    return hashlib.sha256(blob).hexdigest()


def merkle_root_from_path(leaf_hex: str, path: Iterable[MerkleStep]) -> str:
    cur = bytes.fromhex(leaf_hex)

    for step in path:
        sib = bytes.fromhex(step["sibling"])

        if step["dir"] == "L":
            cur = hashlib.sha256(sib + cur).digest()

        elif step["dir"] == "R":
            cur = hashlib.sha256(cur + sib).digest()

        else:
            raise ValueError(f"Invalid dir: {step['dir']!r}")

    return cur.hex()


def canonical_digest_hex(pub: dict[str, Any], merkle_root_hex: str) -> str:
    parts = [
        hashlib.sha256(pub["rid"].encode("utf-8")).hexdigest(),
        pub["smt2_hash"].lower(),
        sha256_hex_utf8(pub["lfsc"]),
    ]

    if pub.get("drat") is not None:
        parts.append(sha256_hex_utf8(pub["drat"]))

    parts.append(merkle_root_hex.lower())

    msg = b"".join(bytes.fromhex(x) for x in parts)

    return hashlib.sha256(msg).hexdigest()


def ed25519_from_b64url(x_b64u: str) -> Ed25519PublicKey:
    pad = "=" * (-len(x_b64u) % 4)

    raw = base64.urlsafe_b64decode(x_b64u + pad)

    return Ed25519PublicKey.from_public_bytes(raw)


# ----Bloki----- BUNDLE (demo)


def make_bundle(
    outdir: Path,
    rid: str,
    lfsc_path: str | None,
    smt2_path: str | None,
    signature_b64u: str | None,
    *,
    allow_missing: bool = True,
    lfsc_text: str | None = None,
    smt2_text: str | None = None,
) -> Path:
    outdir.mkdir(parents=True, exist_ok=True)

    # Materiał: LFSC/SMT2 – z pliku lub inline albo fallback demo

    lfsc = lfsc_text or (
        Path(lfsc_path).read_text(encoding="utf-8") if lfsc_path and Path(lfsc_path).exists() else None
    )

    smt2 = smt2_text or (
        Path(smt2_path).read_text(encoding="utf-8") if smt2_path and Path(smt2_path).exists() else None
    )

    if not allow_missing and (lfsc is None or smt2 is None):
        print("Missing LFSC/SMT2 and --allow-missing not set", file=sys.stderr)

        raise SystemExit(2)

    if lfsc is None:
        lfsc = "(lfsc proof for demo-002)"

    if smt2 is None:
        smt2 = "(set-logic ALL)\n(check-sat)"

    pub = {
        "rid": rid,
        "smt2_hash": hashlib.sha256(smt2.encode("utf-8")).hexdigest(),
        "lfsc": lfsc,
        "drat": None,
    }

    # Ścieżka Merkle – przykład niepusty

    path: list[MerkleStep] = [
        {"sibling": "a" * 64, "dir": "L"},
        {"sibling": "b" * 64, "dir": "R"},
    ]

    rid_hash_hex = hashlib.sha256(rid.encode("utf-8")).hexdigest()

    bundle_hash_hex = compute_bundle_hash_hex(pub)

    leaf_hex = hashlib.sha256(bytes.fromhex(rid_hash_hex) + bytes.fromhex(bundle_hash_hex)).hexdigest()

    merkle_root_hex = merkle_root_from_path(leaf_hex, path)

    digest_hex = canonical_digest_hex(pub | {"merkle_proof": path}, merkle_root_hex)

    # Podpis – jeśli nie podano detached signature, generujemy z PEM (ENV)

    if signature_b64u is None:
        pem_path = os.getenv("ED25519_PRIVKEY_PEM")

        if not pem_path or not Path(pem_path).exists():
            print("Missing ED25519_PRIVKEY_PEM", file=sys.stderr)

            raise SystemExit(2)

        sk_any = serialization.load_pem_private_key(Path(pem_path).read_bytes(), password=None)

        if not isinstance(sk_any, Ed25519PrivateKey):
            print("PEM is not Ed25519 private key", file=sys.stderr)

            raise SystemExit(2)

        sig = sk_any.sign(bytes.fromhex(digest_hex))

        signature_b64u = base64.urlsafe_b64encode(sig).rstrip(b"=").decode()

    out = {
        **pub,
        "merkle_proof": path,
        "signature": signature_b64u,
        "issued_at": "2025-08-19T12:00:00Z",
    }

    out_path = outdir / f"{rid}.json"

    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")

    return out_path


# --- blok --- CLI --------------------------------------------------------------


def _parse_args() -> Any:
    p = ArgumentParser(description="Build demo public bundle (non-empty Merkle path) and sign it.")

    p.add_argument("--rid", help="Resource ID (64-hex). If absent, derived from seed.")

    p.add_argument("--seed", help="Seed text for RID (SHA-256)", default=None)

    p.add_argument("--lfsc", dest="lfsc_path", help="Path to LFSC file", default=None)

    p.add_argument("--smt2", dest="smt2_path", help="Path to SMT2 file", default=None)

    p.add_argument("--signature", help="Detached signature (>= 40 chars)", default=None)

    p.add_argument("--outdir", help="Output dir (defaults to PROOF_BUNDLE_DIR)", default=DEFAULT_DIR)

    p.add_argument("--echo-url", action="store_true", help="Print GET URL for API")

    p.add_argument("--allow-missing", action="store_true", help="Use default text if --lfsc/--smt2 files are missing")

    p.add_argument("--lfsc-text", dest="lfsc_text", default=None, help="Inline LFSC text (overrides --lfsc file)")

    p.add_argument("--smt2-text", dest="smt2_text", default=None, help="Inline SMT2 text (overrides --smt2 file)")

    return p.parse_args()


def main() -> int:
    args = _parse_args()

    # RID resolve

    if args.rid:
        rid = args.rid.strip().lower()

        if not _is_hex64(rid):
            print("[RID] must be 64-hex (lowercase).", flush=True)

            return 2

    else:
        seed = args.seed or "rid-demo"

        rid = _hx_text(seed)

    outdir = Path(args.outdir)

    out_path = make_bundle(
        outdir,
        rid,
        args.lfsc_path,
        args.smt2_path,
        args.signature,
        allow_missing=args.allow_missing,
        lfsc_text=args.lfsc_text,
        smt2_text=args.smt2_text,
    )

    print(f"[OK] bundle written: {out_path}")

    if args.echo_url:
        print(f"[GET] http://127.0.0.1:8000/pco/public/{rid}")

    return 0


# --- blok --- Entrypoint -------------------------------------------------------

if __name__ == "__main__":
    raise SystemExit(main())





# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

