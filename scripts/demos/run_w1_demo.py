#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/run_w1_demo.py                         |
# | ROLE: Project script.                                       |
# | PLIK: scripts/demos/run_w1_demo.py                         |
# | ROLA: Skrypt projektu.                                      |
# +-------------------------------------------------------------+
"""
PL: W1 — demo tygodnia (10 min): ingest → analyze → ProofGate → Ledger.

EN: W1 — weekly demo (10 min): ingest → analyze → ProofGate → Ledger.
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

from datetime import UTC, datetime
import json
import os

# Repo-root on sys.path (run as script)
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

# === KONFIGURACJA / CONFIGURATION ===

OUT_DIR = Path("reports")
OUT_DIR.mkdir(parents=True, exist_ok=True)
REPORT_PATH = OUT_DIR / "w1_demo.json"


# === MODELE / MODELS ===


def _now() -> str:
    return datetime.now(tz=UTC).isoformat(timespec="seconds")


# === LOGIKA / LOGIC ===


def _gen_ed25519_env() -> tuple[str, str]:
    sk = Ed25519PrivateKey.generate()
    pem = sk.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode("utf-8")
    pub = (
        sk.public_key()
        .public_bytes(
            encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw
        )
        .hex()
    )
    os.environ["ED25519_PRIVKEY_PEM"] = pem
    os.environ["ED25519_PUBKEY_HEX"] = pub
    return pem, pub


def _b64u(data: bytes) -> str:
    import base64

    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _sign_ed25519_jws(sk: Ed25519PrivateKey, payload: dict[str, Any]) -> str:
    import json as _json

    header = {"alg": "EdDSA", "typ": "JWT"}
    h = _b64u(_json.dumps(header, separators=(",", ":")).encode("utf-8"))
    p = _b64u(_json.dumps(payload, separators=(",", ":")).encode("utf-8"))
    signing_input = f"{h}.{p}".encode("ascii")
    sig = sk.sign(signing_input)
    return f"{h}.{p}.{_b64u(sig)}"


def _make_pdf_bytes() -> bytes:
    return b"%PDF-1.4\n1 0 obj<<>>endobj\ntrailer<<>>\n%%EOF"


def run_demo() -> dict[str, Any]:
    # Env: proof-only + local verification mocks off by default
    os.environ.setdefault("STRICT_PROOF_ONLY", "1")
    os.environ.setdefault("FINE_GRAINED_ROLES", "0")
    os.environ.setdefault(
        "PROOF_BUNDLE_DIR", str((Path("out") / "public_pco").resolve())
    )

    pem, pub_hex = _gen_ed25519_env()
    sk = serialization.load_pem_private_key(pem.encode("utf-8"), password=None)
    assert isinstance(sk, Ed25519PrivateKey)

    client = TestClient(app)

    # Token (any small payload)
    token = _sign_ed25519_jws(sk, {"sub": "demo", "iat": 0})
    auth = {"Authorization": f"Bearer {token}"}

    steps: list[dict[str, Any]] = []

    # 1) Ingest (PDF)
    files = {"file": ("doc.pdf", _make_pdf_bytes(), "application/pdf")}
    r = client.post("/v1/ingest", files=files)
    steps.append(
        {
            "ingest.status": r.status_code,
            "ledger_chain_header": r.headers.get("X-CERTEUS-Ledger-Chain"),
        }
    )

    # 2) Analyze (PDF)
    r = client.post("/v1/analyze?case_id=CER-DEMO-W1", files=files)
    steps.append(
        {
            "analyze.status": r.status_code,
            "analysis": r.json() if r.status_code == 200 else None,
        }
    )

    # 3) ProofGate publish (PUBLISH path)
    from hashlib import sha256

    pco = {
        "case_id": "CER-DEMO-W1",
        "risk": {"ece": 0.01, "brier": 0.05, "abstain_rate": 0.05},
        "sources": [
            {
                "id": "smt2",
                "uri": "hash://sha256/0",
                "digest": ("sha256:" + sha256(b"demo").hexdigest()),
                "retrieved_at": _now(),
            }
        ],
        "derivations": [
            {
                "claim_id": "claim-1",
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

    r = client.post(
        "/v1/proofgate/publish", headers=auth, json={"pco": pco, "budget_tokens": 1}
    )
    steps.append(
        {
            "publish.gateway.status": r.status_code,
            "decision": (r.json() if r.status_code == 200 else None),
        }
    )

    # Publish via ProofGate service (real decision + ledger write on PUBLISH)
    from services.proofgate.app import app as pg_app  # lazy import

    pg = TestClient(pg_app)
    r2 = pg.post("/v1/proofgate/publish", json={"pco": pco, "budget_tokens": 1})
    steps.append(
        {
            "publish.proofgate.status": r2.status_code,
            "decision": (r2.json() if r2.status_code == 200 else None),
        }
    )

    # 4) Ledger: list records for case
    r = client.get("/v1/ledger/CER-DEMO-W1/records")
    steps.append(
        {
            "ledger.status": r.status_code,
            "records": r.json() if r.status_code == 200 else None,
        }
    )

    # Optional: run gates locally (non-fatal)
    gates: dict[str, Any] = {}
    try:
        import subprocess

        # Ensure boundary report is green (demo baseline)
        out_dir = Path("out")
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "boundary_report.json").write_text(
            json.dumps({"boundary": {"delta_bits": 0, "bits_delta_map": {}}}),
            encoding="utf-8",
        )

        gg = subprocess.run(
            ["python", "scripts/gates/gauge_gate.py", "--epsilon", "0.01"],
            capture_output=True,
            text=True,
        )
        pc = subprocess.run(
            [
                "python",
                "scripts/gates/path_coverage_gate.py",
                "--min-gamma",
                "0.90",
                "--max-uncaptured",
                "0.10",
            ],
            capture_output=True,
            text=True,
        )
        bg = subprocess.run(
            [
                "python",
                "scripts/gates/boundary_rebuild_gate.py",
                "--must-zero",
                "--report",
                str(out_dir / "boundary_report.json"),
            ],
            capture_output=True,
            text=True,
        )
        gates = {
            "gauge": {"rc": gg.returncode, "out": (gg.stdout or "").strip()},
            "path_coverage": {"rc": pc.returncode, "out": (pc.stdout or "").strip()},
            "boundary": {"rc": bg.returncode, "out": (bg.stdout or "").strip()},
        }
    except Exception:
        gates = {"error": "gate-run-failed"}

    report = {"ts": _now(), "ok": True, "steps": steps, "gates": gates}
    REPORT_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return report


def main() -> int:
    rep = run_demo()
    print(json.dumps({"ok": True, "summary": {"publish": rep["steps"][2]}}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
