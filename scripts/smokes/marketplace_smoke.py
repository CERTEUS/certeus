#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smokes/marketplace_smoke.py                  |
# | ROLE: Project script.                                        |
# | PLIK: scripts/smokes/marketplace_smoke.py                  |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+
"""
PL: Lekki smoke Marketplace (verify/install/list) via TestClient -> reports JSON.
EN: Lightweight Marketplace smoke (verify/install/list) via TestClient -> JSON report.
"""

from __future__ import annotations

import base64
import json
import os
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

from services.api_gateway.main import app


def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def main() -> int:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    with TestClient(app) as c:
        # setup key
        sk = Ed25519PrivateKey.generate()
        _pem = sk.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption(),
        ).decode("utf-8")
        pub = sk.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        os.environ["ED25519_PUBKEY_B64URL"] = _b64u(pub)
        # manifest unsigned
        man = Path("plugins/demo_alpha/plugin.yaml").read_text(encoding="utf-8")
        unsigned = "\n".join(
            [ln for ln in man.splitlines() if not ln.strip().startswith("signature:")]
        )
        sig = _b64u(sk.sign(unsigned.encode("utf-8")))
        out = {}
        out["verify"] = c.post(
            "/v1/marketplace/verify_manifest",
            json={"manifest_yaml": unsigned, "signature_b64u": sig},
        ).json()
        out["install"] = c.post(
            "/v1/marketplace/install",
            json={
                "name": "demo_alpha",
                "manifest_yaml": unsigned,
                "signature_b64u": sig,
            },
        ).json()
        out["plugins_len"] = len(c.get("/v1/marketplace/plugins").json() or [])
        (reports / "smoke_marketplace.json").write_text(
            json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8"
        )
    print("smoke_marketplace -> reports/smoke_marketplace.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
