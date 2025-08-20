#!/usr/bin/env python3
# +=====================================================================+
# |                              CERTEUS                                |
# +=====================================================================+
# | FILE: scripts/ed25519_keytool.py                                    |
# | ROLE: Generate Ed25519 keypair and export public key (Base64URL).   |
# +=====================================================================+
from __future__ import annotations

import base64
from argparse import ArgumentParser
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey


def main() -> None:
    ap = ArgumentParser()
    ap.add_argument("--gen", action="store_true")
    ap.add_argument("--out-pem", default="ed25519-private.pem")
    ap.add_argument("--shell", choices=["bash", "powershell"], default="powershell")
    args = ap.parse_args()

    if args.gen:
        sk = Ed25519PrivateKey.generate()
        pem = sk.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption(),
        )
        Path(args.out_pem).write_bytes(pem)
        pk = sk.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        b64u = base64.urlsafe_b64encode(pk).rstrip(b"=").decode()
        if args.shell == "bash":
            print(f'export ED25519_PRIVKEY_PEM="{Path(args.out_pem).resolve()}"')
            print(f'export ED25519_PUBKEY_B64URL="{b64u}"')
        else:
            print(f'$env:ED25519_PRIVKEY_PEM = "{Path(args.out_pem).resolve()}"')
            print(f"$env:ED25519_PUBKEY_B64URL = \"{b64u}\"")
    else:
        # Print Base64URL for an existing PEM (public key)
        ap = ArgumentParser()
        ap.add_argument("--pem", default="ed25519-public.pem")
        args = ap.parse_args()
        raw = Path(args.pem).read_bytes()
        pub = serialization.load_pem_public_key(raw)
        b = pub.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        print(base64.urlsafe_b64encode(b).rstrip(b"=").decode())


if __name__ == "__main__":
    main()
