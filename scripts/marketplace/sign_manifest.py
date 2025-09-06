#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/marketplace/sign_manifest.py                  |
# | ROLE: Dev utility.                                          |
# | PLIK: scripts/marketplace/sign_manifest.py                  |
# | ROLA: Narzędzie dev do podpisywania manifestów pluginów.    |
# +-------------------------------------------------------------+

"""
PL: Podpisuje plik YAML (manifest wtyczki) kluczem Ed25519 → base64url.

EN: Signs a YAML file (plugin manifest) with Ed25519 → base64url signature.

Użycie / Usage:
  $py scripts/marketplace/sign_manifest.py --in plugins/foo/plugin.yaml \
       --key .devkeys/dev_ed25519.pem --print

  # Wstawienie pola `signature: ...` i zapis do pliku:
  $py scripts/marketplace/sign_manifest.py --in plugins/foo/plugin.yaml \
       --key .devkeys/dev_ed25519.pem --embed
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import argparse
import base64
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

# === LOGIKA / LOGIC ===


def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def sign_text(priv_pem: str, text: str) -> str:
    key = serialization.load_pem_private_key(priv_pem.encode("utf-8"), password=None)
    assert isinstance(key, Ed25519PrivateKey)
    sig = key.sign(text.encode("utf-8"))
    return _b64u(sig)


def embed_signature(yaml_text: str, signature_b64u: str) -> str:
    # Dodaj/aktualizuj linię `signature: <b64u>` na końcu (MVP).
    lines = [
        ln for ln in yaml_text.splitlines() if not ln.strip().startswith("signature:")
    ]
    lines.append(f"signature: {signature_b64u}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Sign plugin manifest (YAML) with Ed25519")
    ap.add_argument("--in", dest="in_path", required=True, help="Path to manifest YAML")
    ap.add_argument(
        "--key",
        dest="key_path",
        required=True,
        help="Path to Ed25519 private key (PEM)",
    )
    ap.add_argument(
        "--print",
        dest="do_print",
        action="store_true",
        help="Print signature to stdout",
    )
    ap.add_argument(
        "--embed",
        dest="do_embed",
        action="store_true",
        help="Embed signature into YAML file",
    )
    args = ap.parse_args(argv)

    p = Path(args.in_path)
    pem = Path(args.key_path).read_text(encoding="utf-8")
    raw = p.read_text(encoding="utf-8")

    sig = sign_text(pem, raw)

    if args.do_print or not args.do_embed:
        print(sig)

    if args.do_embed:
        out = embed_signature(raw, sig)
        p.write_text(out, encoding="utf-8")

    return 0


if __name__ == "__main__":  # === I/O / ENDPOINTS ===
    raise SystemExit(main())

# === TESTY / TESTS ===
