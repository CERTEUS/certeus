#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w3_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w3_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W3 — Geodezyjny dowód + lock → publish.

EN: W3 — Geodesic proof + lock → publish.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from datetime import UTC, datetime
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


def _now() -> str:
    return datetime.now(tz=UTC).isoformat(timespec="seconds")


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


def _b64u(data: bytes) -> str:
    import base64

    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _sign_ed25519_jws(sk: Ed25519PrivateKey, payload: dict[str, Any]) -> str:
    header = {"alg": "EdDSA", "typ": "JWT"}
    h = _b64u(json.dumps(header, separators=(",", ":")).encode("utf-8"))
    p = _b64u(json.dumps(payload, separators=(",", ":")).encode("utf-8"))
    signing_input = f"{h}.{p}".encode("ascii")
    sig = sk.sign(signing_input)
    return f"{h}.{p}.{_b64u(sig)}"


def run_demo() -> dict[str, Any]:
    os.environ.setdefault("STRICT_PROOF_ONLY", "1")
    os.environ.setdefault("FINE_GRAINED_ROLES", "0")

    sk = _gen_keys_env()
    token = _sign_ed25519_jws(sk, {"sub": "w3-demo", "iat": 0})
    _ = token  # token available if needed for auth headers

    c = TestClient(app)
    case = "LEX-DEMO-W3"

    # Geodesic
    g = c.post("/v1/cfe/geodesic", json={"case": case, "facts": {}, "norms": {}})
    action = float(g.headers.get("X-CERTEUS-PCO-cfe.geodesic_action") or 0.0)

    # Lock horizon
    h = c.post("/v1/cfe/horizon", json={"case": case, "lock": True})
    locked = (h.headers.get("X-CERTEUS-CFE-Locked") or "false").lower() == "true"
    mass = float(h.headers.get("X-CERTEUS-PCO-cfe.horizon_mass") or 0.0)

    # Derive a simple PCO from CFE signals
    pco = {
        "case_id": case,
        "domain": "lex",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
        "signals": {
            "cfe.geodesic_action": action,
            "cfe.horizon_mass": mass,
            "cfe.locked": locked,
        },
        "sources": [
            {
                "id": "cfe",
                "uri": "cfe://signals",
                "digest": "sha256:" + sha256(json.dumps({"a": action, "m": mass}).encode("utf-8")).hexdigest(),
                "retrieved_at": _now(),
            }
        ],
        "derivations": [
            {
                "claim_id": "claim-cfe",
                "solver": "z3",
                "proof_format": "LFSC",
                "artifact_digest": sha256(b"lfsc").hexdigest(),
            }
        ],
        "reproducibility": {
            "image": os.getenv("CERTEUS_IMAGE", "certeus/local:dev"),
            "image_digest": os.getenv("CERTEUS_IMAGE_DIGEST", "sha256:placeholder"),
            "seed": os.getenv("CERTEUS_SEED", "0"),
        },
        "signatures": [{"role": "counsel", "by": "demo", "sig": "ok"}],
    }

    # Publish via ProofGate
    from services.proofgate.app import app as pg_app  # type: ignore

    pg = TestClient(pg_app)
    pr = pg.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 1})
    status = (pr.json() or {}).get("status") if pr.status_code == 200 else None

    rep = {"case": case, "geodesic_action": action, "locked": locked, "status": status}
    Path("reports").mkdir(parents=True, exist_ok=True)
    Path("reports/w3_demo.json").write_text(json.dumps(rep, indent=2), encoding="utf-8")
    print(json.dumps({"ok": bool(status), "status": status}))
    return rep


def main() -> int:
    run_demo()
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
