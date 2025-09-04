#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w2_audit.py                        |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w2_audit.py                        |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W2 — Audyt bez zaufania: ledger → boundary → podpisy.

EN: W2 — Trustless audit: ledger → boundary → signatures.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from hashlib import sha256
import json
import os
from pathlib import Path, Path as _P
import sys as _sys
from typing import Any

_sys.path.insert(0, str(_P(__file__).resolve().parents[2]))  # noqa: E402

from cryptography.hazmat.primitives import serialization  # noqa: E402
from cryptography.hazmat.primitives.asymmetric.ed25519 import (  # noqa: E402
    Ed25519PrivateKey,
)
from fastapi.testclient import TestClient  # noqa: E402

from services.api_gateway.main import app  # noqa: E402


def _gen_keys_env() -> Ed25519PrivateKey:
    sk = Ed25519PrivateKey.generate()
    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    os.environ["ED25519_PRIVKEY_PEM"] = pem
    os.environ["ED25519_PUBKEY_HEX"] = (
        sk.public_key().public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw).hex()
    )
    return sk


def run() -> dict[str, Any]:
    out_dir = Path("out/demo_w2_audit")
    out_dir.mkdir(parents=True, exist_ok=True)
    os.environ["PROOF_BUNDLE_DIR"] = str(out_dir)

    _ = _gen_keys_env()
    c = TestClient(app)

    rid = "RID-AUDIT-W2"
    body = {
        "rid": rid,
        "smt2_hash": sha256(b"demo-smt").hexdigest(),
        "lfsc": "(lfsc proof)",
        "merkle_proof": [],  # empty path ⇒ root==leaf
    }
    r = c.post("/v1/pco/bundle", json=body)
    assert r.status_code == 200, r.text
    bundle_out = r.json()
    path = bundle_out.get("public_path")

    # Boundary reconstruct
    b = c.get("/v1/boundary/status").json()
    delta = int(b.get("delta_bits", -1))

    # Inspect saved bundle: signature and ledger_ref
    saved = json.loads(Path(path).read_text(encoding="utf-8")) if path else {}
    signature = saved.get("signature") or saved.get("signatures")
    ledger_ref = ((saved.get("ledger") or {}).get("pco_tx_id")) if isinstance(saved.get("ledger"), dict) else None

    rep = {
        "rid": rid,
        "bundle_path": path,
        "delta_bits": delta,
        "has_signature": bool(signature),
        "ledger_ref": ledger_ref,
    }
    Path("reports").mkdir(parents=True, exist_ok=True)
    Path("reports/w2_audit.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(json.dumps({"ok": (delta == 0 and bool(signature)), "delta_bits": delta, "has_signature": bool(signature)}))
    return rep


def main() -> int:
    run()
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
