#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/api_gateway/routers/jwks.py                |
# | ROLE: JWKS endpoint for Ed25519 public keys               |
# | PLIK: services/api_gateway/routers/jwks.py                |
# | ROLA: Endpoint JWKS dla kluczy publicznych Ed25519       |
# +-------------------------------------------------------------+

"""
PL: Router JWKS dla kluczy publicznych Ed25519.
EN: JWKS router for Ed25519 public keys.
"""

from __future__ import annotations

import base64
import hashlib
import os
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from fastapi import APIRouter, HTTPException
from fastapi.responses import JSONResponse

router = APIRouter(tags=["PCO"])


def _get_signing_key() -> Ed25519PrivateKey:
    """Pobiera klucz podpisywania z zmiennej środowiskowej."""
    pem_str = os.getenv("ED25519_PRIVKEY_PEM")
    if not pem_str:
        raise HTTPException(status_code=500, detail="ED25519_PRIVKEY_PEM not configured")

    try:
        # Sprawdź czy to raw hex czy PEM
        if pem_str.startswith("-----"):
            # PEM format
            return serialization.load_pem_private_key(pem_str.encode(), password=None)
        else:
            # Raw hex format
            key_bytes = bytes.fromhex(pem_str)
            return Ed25519PrivateKey.from_private_bytes(key_bytes)
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Invalid signing key: {e}")


def _key_id_from_public_key(public_key: bytes) -> str:
    """Generuje key ID z klucza publicznego."""
    return hashlib.sha256(public_key).hexdigest()[:16]


def _public_key_to_jwk(private_key: Ed25519PrivateKey) -> dict[str, Any]:
    """Konwertuje klucz publiczny Ed25519 do formatu JWK."""

    # Pobierz surowe bajty klucza publicznego
    public_key_bytes = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw
    )

    # Key ID
    kid = _key_id_from_public_key(public_key_bytes)

    # x coordinate (base64url)
    x = base64.urlsafe_b64encode(public_key_bytes).decode('ascii').rstrip('=')

    return {"kty": "OKP", "use": "sig", "kid": kid, "crv": "Ed25519", "x": x, "alg": "EdDSA"}


@router.get(
    "/.well-known/jwks.json",
    summary="Get JWKS with Ed25519 public keys",
    description="Returns JSON Web Key Set with Ed25519 public keys used for PCO signing",
)
def get_jwks() -> dict[str, Any]:
    """
    PL: Zwraca JSON Web Key Set z kluczami publicznymi Ed25519.
    EN: Returns JSON Web Key Set with Ed25519 public keys.
    """

    try:
        signing_key = _get_signing_key()
        jwk = _public_key_to_jwk(signing_key)

        jwks = {"keys": [jwk]}

        return JSONResponse(
            content=jwks,
            headers={
                "Content-Type": "application/json",
                "Cache-Control": "public, max-age=3600",  # 1 hour cache
                "Access-Control-Allow-Origin": "*",
            },
        )

    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Failed to generate JWKS: {str(e)}")


@router.get(
    "/.well-known/certeus-metadata",
    summary="Get CERTEUS metadata",
    description="Returns CERTEUS-specific metadata including supported versions and capabilities",
)
def get_certeus_metadata() -> dict[str, Any]:
    """
    PL: Zwraca metadane CERTEUS z obsługiwanymi wersjami i możliwościami.
    EN: Returns CERTEUS metadata with supported versions and capabilities.
    """

    return {
        "issuer": "https://certeus.dev",
        "pco_versions_supported": ["1.0", "0.2"],
        "proof_formats_supported": ["LFSC", "DRAT", "ALETHE"],
        "signature_algorithms_supported": ["ed25519", "p256", "p384"],
        "evidence_graph_formats": ["prov-json-ld", "ro-crate"],
        "endpoints": {
            "pco_bundle": "/v1/pco/bundle",
            "pco_public": "/v1/pco/public/{case_id}",
            "verify": "/v1/verify",
            "jwks": "/.well-known/jwks.json",
        },
        "compliance": ["gdpr", "prov-w3c", "json-schema-draft-2020-12"],
        "features": {
            "pii_redaction": True,
            "evidence_graph": True,
            "formal_verification": True,
            "tsa_timestamps": True,
            "quantum_resistance": False,  # Future feature
        },
    }
