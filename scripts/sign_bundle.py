# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: scripts/sign_bundle.py                              |

# | ROLE: Project module.                                       |

# | PLIK: scripts/sign_bundle.py                              |

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

import hashlib

import json

import os

from pathlib import Path

from typing import Any, cast

from cryptography.hazmat.primitives import serialization

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===












































# +=====================================================================+



# |                              CERTEUS                                |



# +=====================================================================+



# | FILE: scripts/sign_bundle.py                                        |



# | ROLE: Sign public PCO bundle (Ed25519 detached signature)           |



# +=====================================================================+



# ----Bloki----- IMPORTY





# ----Bloki----- FUNKCJE





def sha256_hex_utf8(s: str) -> str:

    return hashlib.sha256(s.encode("utf-8")).hexdigest()





def compute_bundle_hash_hex(pub: dict[str, Any]) -> str:

    payload = {"smt2_hash": pub["smt2_hash"], "lfsc_sha256": sha256_hex_utf8(pub["lfsc"])}



    if pub.get("drat") is not None:

        payload["drat_sha256"] = sha256_hex_utf8(pub["drat"])



    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")



    return hashlib.sha256(blob).hexdigest()





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





# ----Bloki----- MAIN





def main() -> None:

    ap = ArgumentParser(description="Sign public PCO bundle (Ed25519 detached signature).")



    ap.add_argument("--rid", required=True)



    ap.add_argument("--bundle-dir", default=os.getenv("PROOF_BUNDLE_DIR", "./data/public_pco"))



    ap.add_argument("--key", default="ed25519-private.pem", help="PEM private key (PKCS8, no password)")



    args = ap.parse_args()



    bundle_path = Path(args.bundle_dir) / f"{args.rid}.json"



    # Czytaj 'utf-8-sig' (leczy BOM); zapisz bez BOM



    pub = json.loads(bundle_path.read_text(encoding="utf-8-sig"))



    # Merkle (MVP): path=[] → root = leaf



    bundle_hash_hex = compute_bundle_hash_hex(pub)



    rid_hash_hex = hashlib.sha256(pub["rid"].encode("utf-8")).hexdigest()



    leaf_hex = hashlib.sha256(bytes.fromhex(rid_hash_hex) + bytes.fromhex(bundle_hash_hex)).hexdigest()



    merkle_root_hex = leaf_hex



    digest_hex = canonical_digest_hex(pub, merkle_root_hex)



    sk_any = serialization.load_pem_private_key(Path(args.key).read_bytes(), password=None)



    if not isinstance(sk_any, Ed25519PrivateKey):

        raise TypeError("Loaded key is not Ed25519 (expected Ed25519PrivateKey).")



    sk = cast(Ed25519PrivateKey, sk_any)



    sig = sk.sign(bytes.fromhex(digest_hex))



    pub["signature"] = base64.urlsafe_b64encode(sig).rstrip(b"=").decode()



    bundle_path.write_text(json.dumps(pub, ensure_ascii=False, indent=2), encoding="utf-8")



    print(f"OK: signed {bundle_path}")





if __name__ == "__main__":

    main()











# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

