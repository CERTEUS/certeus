#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/gates/spiffe_gate.py                         |
# | ROLE: SPIFFE SVID structure gate (JWT/X509)                |
# +-------------------------------------------------------------+

from __future__ import annotations

import base64
import json
import os
from pathlib import Path
from typing import Any


def _is_on(v: str | None) -> bool:
    return (v or "").strip().lower() in {"1", "true", "on", "yes"}


def _b64url_pad(s: str) -> str:
    return s + "=" * (-len(s) % 4)


def _check_jwt(path: Path) -> bool:
    try:
        s = path.read_text(encoding="utf-8").strip()
        parts = s.split(".")
        if len(parts) < 2:
            return False
        payload_raw = base64.urlsafe_b64decode(_b64url_pad(parts[1]))
        obj = json.loads(payload_raw)
        sub = str((obj.get("sub") or "").strip())
        return sub.startswith("spiffe://")
    except Exception:
        return False


def _check_x509(path: Path) -> bool:
    try:
        from cryptography import x509  # type: ignore
        from cryptography.hazmat.backends import default_backend  # type: ignore
        from cryptography.x509.oid import ExtensionOID  # type: ignore

        data = path.read_bytes()
        try:
            cert = x509.load_pem_x509_certificate(data, default_backend())
        except Exception:
            cert = x509.load_der_x509_certificate(data, default_backend())
        try:
            san = cert.extensions.get_extension_for_oid(ExtensionOID.SUBJECT_ALTERNATIVE_NAME).value
            for uri in san.get_values_for_type(x509.UniformResourceIdentifier):
                if str(uri).startswith("spiffe://"):
                    return True
        except Exception:
            return False
        return False
    except Exception:
        return False


def main() -> int:
    repo = Path(".").resolve()
    jwt = Path(os.getenv("SPIFFE_SVID_JWT") or (repo / "data" / "spiffe" / "svid.jwt"))
    x509p = Path(os.getenv("SPIFFE_SVID_X509") or (repo / "data" / "spiffe" / "svid.pem"))
    ok = False
    if jwt.exists():
        ok = ok or _check_jwt(jwt)
    if x509p.exists():
        ok = ok or _check_x509(x509p)
    if ok:
        print("SPIFFE Gate: OK")
        return 0
    print("SPIFFE Gate: FAIL (no valid SVID)")
    return 3


if __name__ == "__main__":
    raise SystemExit(main())

