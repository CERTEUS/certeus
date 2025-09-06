# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/verify_bundle.py                            |

# | ROLE: Project module.                                       |

# | PLIK: scripts/verify_bundle.py                            |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

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
from typing import Any, TypedDict, cast

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===


class MerkleStep(TypedDict):
    sibling: str  # hex

    dir: str  # 'L' | 'R'


# === LOGIKA / LOGIC ===

# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: scripts/verify_bundle.py                                      |

# | ROLE: Verify public PCO bundle (Merkle + canonical digest + Ed25519)|

# +=====================================================================+

# Opis:

# - Weryfikuje publiczny bundle PCO (0 PII): struktura, Merkle, podpis.

# - Obsługa Merkle path: MVP [] oraz pełna ścieżka [{sibling, dir:'L'|'R'}].

# - Kanoniczny digest: sha256( rid_hash || smt2_hash || lfsc_sha256 || [drat_sha256] || merkle_root ).

# - Podpis: Ed25519 (Base64URL, bez "="); klucz publiczny z --pub-b64url lub ENV ED25519_PUBKEY_B64URL.

# - Zwraca kod wyjścia: 0 OK, 2 błąd weryfikacji/IO.

#

# Użycie (CLI):

#   python scripts/verify_bundle.py --rid demo-001 \

#       --bundle-dir ./data/public_pco \

#       --pub-b64url $env:ED25519_PUBKEY_B64URL

#

# Wymagania:

#   - Python 3.11+, pakiet 'cryptography'

#   - JSON bez BOM (lub czytany 'utf-8-sig')

#

# Konwencje:

#   - future → stdlib (import, from) → third-party (import, from)

#   - typy: dict[str, Any], list[str] itd. (PEP 585)

#   - linia: max 120

# ----Bloki----- IMPORTY

# ----Bloki----- TYPY

# ----Bloki----- POMOCNICZE


def sha256_hex_utf8(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def is_hex64(x: str) -> bool:
    return (
        isinstance(x, str)
        and len(x) == 64
        and all(c in "0123456789abcdef" for c in x.lower())
    )


def compute_bundle_hash_hex(pub: dict[str, Any]) -> str:
    payload = {
        "smt2_hash": pub["smt2_hash"],
        "lfsc_sha256": sha256_hex_utf8(pub["lfsc"]),
    }

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


# ----Bloki----- MAIN


def main() -> int:
    ap = ArgumentParser(
        description="Verify public PCO bundle (Merkle + Ed25519 signature)."
    )

    ap.add_argument("--rid", required=True)

    ap.add_argument(
        "--bundle-dir", default=os.getenv("PROOF_BUNDLE_DIR", "./data/public_pco")
    )

    ap.add_argument("--pub-b64url", default=os.getenv("ED25519_PUBKEY_B64URL"))

    args = ap.parse_args()

    if not args.pub_b64url:
        print(
            "ERR: missing public key (use --pub-b64url or ED25519_PUBKEY_B64URL)",
            file=sys.stderr,
        )

        return 2

    bundle_path = Path(args.bundle_dir) / f"{args.rid}.json"

    try:
        pub = json.loads(bundle_path.read_text(encoding="utf-8-sig"))

    except Exception as e:  # noqa: BLE001
        print(f"ERR: cannot read bundle: {e}", file=sys.stderr)

        return 2

    # Sanity checks

    if not is_hex64(pub.get("smt2_hash", "")):
        print("ERR: smt2_hash must be 64 hex chars", file=sys.stderr)

        return 2

    # 1) leaf := sha256( rid_hash || bundle_hash )

    rid_hash_hex = hashlib.sha256(pub["rid"].encode("utf-8")).hexdigest()

    bundle_hash_hex = compute_bundle_hash_hex(pub)

    leaf_hex = hashlib.sha256(
        bytes.fromhex(rid_hash_hex) + bytes.fromhex(bundle_hash_hex)
    ).hexdigest()

    # 2) merkle_root (MVP: path może być [] lub L/R ścieżka)

    path = pub.get("merkle_proof") or []

    merkle_root_hex = merkle_root_from_path(leaf_hex, cast(Iterable[MerkleStep], path))

    # 3) canonical digest

    digest_hex = canonical_digest_hex(pub, merkle_root_hex)

    # 4) verify signature

    try:
        pk = ed25519_from_b64url(cast(str, args.pub_b64url))

        sig_b64u = pub.get("signature", "")

        pad = "=" * (-len(sig_b64u) % 4)

        sig = base64.urlsafe_b64decode(sig_b64u + pad)

        pk.verify(sig, bytes.fromhex(digest_hex))

    except Exception as e:  # noqa: BLE001
        print(f"ERR: signature invalid: {e}", file=sys.stderr)

        return 2

    print(f"OK: {bundle_path} verified")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
