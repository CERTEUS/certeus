#!/usr/bin/env python3

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/make_pco_bundle.py                          |

# | ROLE: Project module.                                       |

# | PLIK: scripts/make_pco_bundle.py                          |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+


r"""

Użycie / Usage (PowerShell):

  # 1) na podstawie "seed" (RID = sha256(seed))

  uv run python scripts/make_pco_bundle.py --seed rid-demo



  # 2) z własnym RID (64-hex), LFSC i SMT2 z plików

  uv run python scripts/make_pco_bundle.py `

    --rid 0123...cafe `

    --lfsc F:\dowody\proof.lfsc `

    --smt2 F:\modele\model.smt2 `

    --signature 0f0f...



  # 3) od razu pokaż URL GET dla API

  uv run python scripts/make_pco_bundle.py --seed case-42 --echo-url



Domyślny katalog wyjściowy:

  PROOF_BUNDLE_DIR lub ./data/public_pco (utworzy się automatycznie)



Zawartość bundla (minimal):

  {

    "rid": <64-hex>,

    "smt2_hash": <sha256 hexdigest pliku/tekstu SMT2>,

    "lfsc": "(proof ...)" lub zawartość pliku LFSC,

    "merkle_proof": { "root": <leaf>, "leaf": <leaf>, "path": [] },

    "signature": "0"*64 (lub podany)

  }



Weryfikacja:

  curl http://127.0.0.1:8000/pco/public/<rid>

"""


# --- blok --- Importy ----------------------------------------------------------

from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
from typing import Final

# --- blok --- Stałe ------------------------------------------------------------


DEFAULT_DIR: Final[str] = os.getenv("PROOF_BUNDLE_DIR", "./data/public_pco")


# --- blok --- Hash utils -------------------------------------------------------


def _hx_bytes(data: bytes) -> str:
    """sha256 -> hex."""

    return sha256(data).hexdigest()


def _hx_text(text: str) -> str:
    """sha256(utf-8) -> hex."""

    return _hx_bytes(text.encode("utf-8"))


def _is_hex64(s: str) -> bool:
    """Czy ciąg jest 64-znakowym heksadecymalnym ID (lowercase)."""

    return len(s) == 64 and all(c in "0123456789abcdef" for c in s)


def _compute_leaf(rid_hex: str, smt2_hex: str) -> str:
    """

    Minimalny wariant z testów E2E:

    leaf = sha256( (rid_hex + smt2_hex).encode("utf-8") )

    """

    return _hx_text(rid_hex + smt2_hex)


# --- blok --- Bundle build -----------------------------------------------------


def _read_or_default(
    path: str | None,
    default_text: str,
    *,
    allow_missing: bool = False,
    inline_text: str | None = None,
) -> tuple[str, str]:
    """

    Zwraca (content_text, sha256_hex).

    Priorytet: inline_text > plik(path) > default_text (gdy allow_missing lub brak path).

    """

    if inline_text is not None:
        return inline_text, _hx_text(inline_text)

    if path:
        p = Path(path)

        try:
            text = p.read_text(encoding="utf-8")

            return text, _hx_text(text)

        except FileNotFoundError:
            if allow_missing:
                text = default_text

                return text, _hx_text(text)

            raise

    text = default_text

    return text, _hx_text(text)


def make_bundle(
    outdir: Path,
    rid: str,
    lfsc_path: str | None,
    smt2_path: str | None,
    signature: str | None,
    *,
    allow_missing: bool = False,
    lfsc_text: str | None = None,
    smt2_text: str | None = None,
) -> Path:
    outdir.mkdir(parents=True, exist_ok=True)

    # LFSC & SMT2 (treść + hash SMT2)

    lfsc_text_val, _ = _read_or_default(
        lfsc_path,
        "(proof ...)",
        allow_missing=allow_missing,
        inline_text=lfsc_text,
    )

    _, smt2_hex = _read_or_default(
        smt2_path,
        "(set-logic QF_UF) ...",
        allow_missing=allow_missing,
        inline_text=smt2_text,
    )

    # Merkle minimal: root == leaf, brak ścieżki

    leaf = _compute_leaf(rid, smt2_hex)

    merkle_proof = {"root": leaf, "leaf": leaf, "path": []}

    # Podpis: >= 40 znaków (domyślnie 64 zera)

    sig = signature if (signature and len(signature) >= 40) else ("0" * 64)

    bundle = {
        "rid": rid,
        "smt2_hash": smt2_hex,
        "lfsc": lfsc_text_val,
        "merkle_proof": merkle_proof,
        "signature": sig,
    }

    out_path = outdir / f"{rid}.json"

    out_path.write_text(
        json.dumps(bundle, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    return out_path


# --- blok --- CLI --------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="make_pco_bundle",
        description="Create a minimal public PCO bundle JSON (0 PII).",
    )

    rid_grp = p.add_mutually_exclusive_group(required=False)

    rid_grp.add_argument("--rid", help="RID (64-hex). If not provided, use --seed")

    rid_grp.add_argument("--seed", help="Seed string -> RID = sha256(seed)")

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
