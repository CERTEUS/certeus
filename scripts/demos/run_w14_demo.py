#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w14_demo.py                         |
# | ROLE: Local demo runner (no server).                         |
# | PLIK: scripts/demos/run_w14_demo.py                         |
# | ROLA: Lokalne demo W14 przez TestClient (Marketplace/Billing). |
# +-------------------------------------------------------------+

"""
PL: Uruchamia lokalne demo W14 bez serwera: Marketplace (verify/install/list)
    oraz Billing (quota/balance/allocate/refund). Wyniki zapisuje do `reports/`.

EN: Runs W14 local demo without a server using FastAPI TestClient: Marketplace
    (verify/install/list) and Billing (quota/balance/allocate/refund). Stores
    results in `reports/`.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import base64
import json
import os
from pathlib import Path, Path as _P
import sys as _sys
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi.testclient import TestClient

# Ensure repo root on sys.path for local module imports
_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))

from services.api_gateway.main import app

# === LOGIKA / LOGIC ===


def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def gen_keypair() -> tuple[str, str]:
    sk = Ed25519PrivateKey.generate()
    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    pub = sk.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    return pem, _b64u(pub)


def run_marketplace_demo(client: TestClient) -> dict[str, Any]:
    # WARNING: For demo purposes only - in production, use secure key storage
    pem, pub_b64u = gen_keypair()
    os.environ["ED25519_PUBKEY_B64URL"] = pub_b64u

    man_path = Path("plugins/demo_alpha/plugin.yaml")
    manifest = man_path.read_text(encoding="utf-8")
    # Usuń linię signature: jeśli istnieje
    unsigned = "\n".join([ln for ln in manifest.splitlines() if not ln.strip().startswith("signature:")])

    sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
    sig = _b64u(sk.sign(unsigned.encode("utf-8")))

    out: dict[str, Any] = {}

    r_ver = client.post(
        "/v1/marketplace/verify_manifest",
        json={"manifest_yaml": unsigned, "signature_b64u": sig},
    )
    out["alpha_verify"] = {"status": r_ver.status_code, "body": r_ver.json()}

    r_inst = client.post(
        "/v1/marketplace/install",
        json={"name": "demo_alpha", "manifest_yaml": unsigned, "signature_b64u": sig},
    )
    out["alpha_install"] = {"status": r_inst.status_code, "body": r_inst.json()}

    # demo_beta
    man_path_b = Path("plugins/demo_beta/plugin.yaml")
    manifest_b = man_path_b.read_text(encoding="utf-8")
    unsigned_b = "\n".join([ln for ln in manifest_b.splitlines() if not ln.strip().startswith("signature:")])
    sig_b = _b64u(sk.sign(unsigned_b.encode("utf-8")))
    r_ver_b = client.post(
        "/v1/marketplace/verify_manifest",
        json={"manifest_yaml": unsigned_b, "signature_b64u": sig_b},
    )
    out["beta_verify"] = {"status": r_ver_b.status_code, "body": r_ver_b.json()}
    r_inst_b = client.post(
        "/v1/marketplace/install",
        json={
            "name": "demo_beta",
            "manifest_yaml": unsigned_b,
            "signature_b64u": sig_b,
        },
    )
    out["beta_install"] = {"status": r_inst_b.status_code, "body": r_inst_b.json()}

    r_list = client.get("/v1/marketplace/plugins")
    out["plugins"] = {"status": r_list.status_code, "body": r_list.json()}

    return out


def run_billing_demo(client: TestClient) -> dict[str, Any]:
    tenant = "acme"
    out: dict[str, Any] = {}
    r_quota = client.post("/v1/billing/quota", json={"tenant": tenant, "units": 100})
    r_bal1 = client.get("/v1/billing/balance", headers={"X-Tenant-ID": tenant})
    r_alloc = client.post("/v1/billing/allocate", json={"units": 25}, headers={"X-Tenant-ID": tenant})
    r_ref = client.post("/v1/billing/refund", json={"tenant": tenant, "units": 5})
    r_bal2 = client.get("/v1/billing/balance", headers={"X-Tenant-ID": tenant})
    out["quota"] = {"status": r_quota.status_code, "body": r_quota.json()}
    out["balance_before"] = {"status": r_bal1.status_code, "body": r_bal1.json()}
    out["allocate"] = {"status": r_alloc.status_code, "body": r_alloc.json()}
    out["refund"] = {"status": r_ref.status_code, "body": r_ref.json()}
    out["balance_after"] = {"status": r_bal2.status_code, "body": r_bal2.json()}
    return out


def main() -> int:
    reports = Path("reports")
    reports.mkdir(parents=True, exist_ok=True)

    with TestClient(app) as client:
        mp = run_marketplace_demo(client)
        (reports / "w14_marketplace.json").write_text(json.dumps(mp, indent=2, ensure_ascii=False), encoding="utf-8")

        bill = run_billing_demo(client)
        (reports / "w14_billing.json").write_text(json.dumps(bill, indent=2, ensure_ascii=False), encoding="utf-8")

    print("W14 demo outputs -> reports/w14_marketplace.json, reports/w14_billing.json")
    return 0


if __name__ == "__main__":  # === I/O / ENDPOINTS ===
    raise SystemExit(main())

# === TESTY / TESTS ===
