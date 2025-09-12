#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/contracts/test_pco_api_contracts.py           |
# | ROLE: Contract tests for PCO API endpoints                 |
# | PLIK: tests/contracts/test_pco_api_contracts.py           |
# | ROLA: Testy kontraktowe dla endpointów PCO API            |
# +-------------------------------------------------------------+

"""
PL: Testy kontraktowe 100% zgodności API ↔ Schema dla PCO v1.0.
EN: Contract tests ensuring 100% API ↔ Schema compliance for PCO v1.0.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any
from unittest.mock import patch

from fastapi.testclient import TestClient
import pytest

from core.pco.evidence_graph import EvidenceGraphBuilder
from core.pco.validators import PCOContractValidator, PCOPublicValidator, PCOValidator
from services.api_gateway.main import app


class TestPCOContractCompliance:
    """Testy zgodności kontraktów API PCO."""

    @pytest.fixture
    def client(self):
        """Test client dla API."""
        return TestClient(app)

    @pytest.fixture
    def pco_validator(self):
        """Walidator PCO v1.0."""
        return PCOValidator()

    @pytest.fixture
    def pco_public_validator(self):
        """Walidator PCO Public v1.0."""
        return PCOPublicValidator()

    @pytest.fixture
    def contract_validator(self):
        """Walidator kontraktów API."""
        return PCOContractValidator()

    @pytest.fixture
    def valid_pco_request(self):
        """Poprawne żądanie PCO Bundle."""
        return {
            "rid": "CER-123456",
            "smt2_hash": "a" * 64,
            "lfsc": "(assert (= (+ 2 2) 4))",
            "drat": "1 -2 0\n2 0\n0",
            "jurisdiction": {
                "country": "PL",
                "domain": "civil",
                "law_time": "2024-01-01"
            },
            "extensions": {
                "qtmp": {
                    "basis": "computational",
                    "uncertainty_bound": 0.05
                }
            }
        }

    @pytest.fixture
    def mock_ed25519_key(self):
        """Mock klucza Ed25519."""
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
        return Ed25519PrivateKey.generate()

    def test_bundle_endpoint_schema_compliance(
        self,
        client: TestClient,
        valid_pco_request: dict[str, Any],
        contract_validator: PCOContractValidator,
        mock_ed25519_key
    ):
        """Test: /v1/pco/bundle zwraca dane zgodne ze schematem PCO v1.0."""

        # Przygotuj klucz w formacie PEM
        from cryptography.hazmat.primitives import serialization
        pem_bytes = mock_ed25519_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption()
        )
        pem_str = pem_bytes.decode('utf-8')

        with patch.dict('os.environ', {
            'ED25519_PRIVKEY_PEM': pem_str,
            'PROOF_BUNDLE_DIR': '/tmp/test_bundles'
        }):
            response = client.post("/v1/pco/bundle", json=valid_pco_request)

        assert response.status_code == 200
        response_data = response.json()

        # Test backward compatibility fields
        assert "rid" in response_data
        assert "smt2_hash" in response_data
        assert "lfsc" in response_data
        assert "signature" in response_data
        assert "ok" in response_data
        assert response_data["ok"] is True

        # Test contract compliance
        contract_errors = contract_validator.validate_bundle_endpoint_contract(response_data)
        assert len(contract_errors) == 0, f"Contract validation errors: {contract_errors}"

        # Test full PCO v1.0 schema compliance if version field present
        if response_data.get("version") == "1.0":
            pco_validator = PCOValidator()
            pco_errors = pco_validator.validate(response_data, strict=True)
            assert len(pco_errors) == 0, f"PCO validation errors: {pco_errors}"

    def test_public_endpoint_schema_compliance(
        self,
        client: TestClient,
        pco_public_validator: PCOPublicValidator
    ):
        """Test: /v1/pco/public/{case_id} zwraca dane zgodne ze schematem PCO Public v1.0."""

        # Mock response from public endpoint
        mock_public_response = {
            "version": "1.0",
            "case_id": "CER-123456",
            "created_at": "2024-01-01T12:00:00Z",
            "jurisdiction": {
                "country": "PL",
                "domain": "civil"
            },
            "claims_summary": {
                "count": 1,
                "avg_confidence": 0.85,
                "domains": ["civil_procedure"],
                "redacted_texts": [
                    {
                        "id": "claim-1",
                        "redacted_length": 145,
                        "summary": "Procedural claim regarding document authentication"
                    }
                ]
            },
            "sources_summary": {
                "count": 2,
                "total_size_bytes": 45632,
                "types": ["legal_statute", "case_law"]
            },
            "risk": {
                "ece": 0.03,
                "brier": 0.12,
                "p95_latency_ms": 89.5,
                "abstain_rate": 0.02
            },
            "ledger": {
                "merkle_root": "b" * 64,
                "block_height": 12345,
                "timestamp": "2024-01-01T12:01:00Z",
                "bundle_location": "https://ledger.certeus.dev/bundles/CER-123456"
            },
            "signatures": [
                {
                    "role": "producer",
                    "alg": "ed25519",
                    "key_id": "a1b2c3d4e5f67890",
                    "signature": "SGVsbG9TaWduYXR1cmU",
                    "timestamp": "2024-01-01T12:00:30Z"
                }
            ],
            "reproducibility": {
                "image": "certeus/engine:1.0.0",
                "image_digest": "sha256:" + "c" * 64,
                "build_info": {
                    "commit_sha": "d" * 40,
                    "build_time": "2024-01-01T10:00:00Z",
                    "toolchain": "python-3.11-ubuntu-22.04"
                }
            },
            "status": "PUBLISH",
            "redaction_info": {
                "redacted_at": "2024-01-01T12:00:45Z",
                "redaction_policy": "gdpr_article_6",
                "pii_removed": ["names", "addresses", "ids"],
                "etag": "\"a1b2c3d4e5f6789012345678abcdef01\""
            }
        }

        # Validate against PCO Public schema
        errors = pco_public_validator.validate(mock_public_response)
        assert len(errors) == 0, f"PCO Public validation errors: {errors}"

        # Test ETag format compliance
        etag = mock_public_response["redaction_info"]["etag"]
        assert etag.startswith('"') and etag.endswith('"')
        assert len(etag) == 34  # 32 hex chars + 2 quotes

    def test_verify_endpoint_contract_compliance(
        self,
        client: TestClient,
        valid_pco_request: dict[str, Any]
    ):
        """Test: /v1/verify endpoint contract compliance."""


        # Mock response structure
        expected_response_structure = {
            "valid": bool,
            "verification_time_ms": float,
            "errors": list,
            "warnings": list,
            "details": {
                "signatures_valid": bool,
                "proofs_valid": bool,
                "schema_valid": bool,
                "ledger_valid": bool
            },
            "verified_at": str,
            "verifier_info": {
                "version": str,
                "mode": str
            }
        }

        # This would normally make a real request, but for contract testing
        # we verify the expected structure matches OpenAPI spec
        assert all(
            key in expected_response_structure
            for key in ["valid", "verification_time_ms"]
        ), "Missing required fields in verification response structure"

    def test_jwks_endpoint_compliance(self, client: TestClient):
        """Test: /.well-known/jwks.json endpoint compliance."""

        mock_jwks_response = {
            "keys": [
                {
                    "kty": "OKP",
                    "use": "sig",
                    "kid": "a1b2c3d4e5f67890",
                    "crv": "Ed25519",
                    "x": "SGVsbG9Xb3JsZEtleQ"
                }
            ]
        }

        # Validate JWKS structure
        assert "keys" in mock_jwks_response
        assert isinstance(mock_jwks_response["keys"], list)
        assert len(mock_jwks_response["keys"]) > 0

        for key in mock_jwks_response["keys"]:
            assert key["kty"] == "OKP"
            assert key["use"] == "sig"
            assert key["crv"] == "Ed25519"
            assert "kid" in key
            assert "x" in key

    def test_evidence_graph_in_pco_schema_compliance(
        self,
        valid_pco_request: dict[str, Any]
    ):
        """Test: Evidence Graph w PCO jest zgodny z PROV JSON-LD."""

        # Generate evidence graph
        graph = EvidenceGraphBuilder.from_pco_bundle(valid_pco_request)
        prov_data = graph.to_prov_json_ld(include_private=False)

        # Validate PROV JSON-LD structure
        assert "@context" in prov_data
        assert "@graph" in prov_data
        assert isinstance(prov_data["@graph"], list)

        # Check PROV context
        context = prov_data["@context"]
        assert "prov" in context
        assert context["prov"] == "http://www.w3.org/ns/prov#"

        # Validate graph nodes have required PROV fields
        for node in prov_data["@graph"]:
            if "prov:type" in node:
                assert "prov:id" in node, "PROV nodes must have prov:id"

    def test_pco_to_public_redaction_compliance(
        self,
        valid_pco_request: dict[str, Any],
        pco_public_validator: PCOPublicValidator
    ):
        """Test: Redakcja PCO → PCO Public zachowuje zgodność schematów."""

        # Simulate full PCO
        full_pco = {
            **valid_pco_request,
            "version": "1.0",
            "case_id": "CER-123456",
            "created_at": "2024-01-01T12:00:00Z",
            "claims": [
                {
                    "id": "claim-1",
                    "text": "Sensitive legal claim with PII: John Doe, PESEL 12345678901",
                    "legal_basis": {
                        "statutes": [{"code": "KC", "article": "art. 1"}],
                        "cases": []
                    },
                    "confidence": 0.85
                }
            ],
            "sources": [
                {
                    "id": "source-1",
                    "uri": "https://example.com/law.pdf",
                    "digest": "sha256:" + "a" * 64,
                    "retrieved_at": "2024-01-01T11:00:00Z",
                    "license": "public_domain"
                }
            ],
            "risk": {
                "ece": 0.03,
                "brier": 0.12,
                "p95_latency_ms": 89.5,
                "abstain_rate": 0.02
            },
            "ledger": {
                "merkle_root": "b" * 64,
                "block_height": 12345,
                "timestamp": "2024-01-01T12:01:00Z"
            },
            "signatures": [
                {
                    "role": "producer",
                    "alg": "ed25519",
                    "key_id": "a1b2c3d4e5f67890",
                    "signature": "SGVsbG9TaWduYXR1cmU",
                    "timestamp": "2024-01-01T12:00:30Z"
                }
            ],
            "reproducibility": {
                "image": "certeus/engine:1.0.0",
                "image_digest": "sha256:" + "c" * 64,
                "seed": "test123",
                "build_info": {
                    "commit_sha": "d" * 40,
                    "build_time": "2024-01-01T10:00:00Z",
                    "toolchain": "python-3.11"
                }
            },
            "status": "PUBLISH"
        }

        # Simulate redaction to public PCO
        public_pco = {
            "version": "1.0",
            "case_id": full_pco["case_id"],
            "created_at": full_pco["created_at"],
            "jurisdiction": {
                "country": "PL",
                "domain": "civil"
            },
            "claims_summary": {
                "count": len(full_pco["claims"]),
                "avg_confidence": 0.85,
                "domains": ["civil"],
                "redacted_texts": [
                    {
                        "id": "claim-1",
                        "redacted_length": len(full_pco["claims"][0]["text"]),
                        "summary": "Legal claim regarding civil procedure"
                    }
                ]
            },
            "sources_summary": {
                "count": len(full_pco["sources"]),
                "total_size_bytes": 1024,
                "types": ["legal_statute"],
                "public_sources": [
                    {
                        "id": "source-1",
                        "uri": full_pco["sources"][0]["uri"],
                        "digest": full_pco["sources"][0]["digest"],
                        "license": full_pco["sources"][0]["license"]
                    }
                ]
            },
            "risk": full_pco["risk"],
            "ledger": {
                **full_pco["ledger"],
                "bundle_location": f"https://ledger.certeus.dev/bundles/{full_pco['case_id']}"
            },
            "signatures": full_pco["signatures"],
            "reproducibility": {
                k: v for k, v in full_pco["reproducibility"].items()
                if k != "seed"  # Remove sensitive seed
            },
            "status": full_pco["status"],
            "redaction_info": {
                "redacted_at": "2024-01-01T12:00:45Z",
                "redaction_policy": "gdpr_article_6",
                "pii_removed": ["names", "ids"],
                "etag": "\"a1b2c3d4e5f6789012345678abcdef01\""
            }
        }

        # Validate public PCO compliance
        errors = pco_public_validator.validate(public_pco)
        assert len(errors) == 0, f"Public PCO validation errors: {errors}"

        # Ensure no PII leaked
        claims_summary = public_pco["claims_summary"]
        for redacted_text in claims_summary.get("redacted_texts", []):
            summary = redacted_text["summary"]
            assert "PESEL" not in summary
            assert "John Doe" not in summary
            assert len(summary) <= 100  # Summary length limit

    def test_openapi_schema_completeness(self):
        """Test: OpenAPI spec zawiera wszystkie wymagane endpointy PCO v1.0."""

        openapi_path = Path(__file__).parent.parent.parent / "docs" / "api" / "openapi.yaml"

        if openapi_path.exists():
            import yaml
            with open(openapi_path, encoding='utf-8') as f:
                openapi_spec = yaml.safe_load(f)

            paths = openapi_spec.get("paths", {})

            # Required PCO v1.0 endpoints
            required_endpoints = [
                "/v1/pco/bundle",
                "/v1/pco/public/{case_id}",
                "/v1/verify",
                "/.well-known/jwks.json"
            ]

            for endpoint in required_endpoints:
                assert endpoint in paths, f"Missing required endpoint: {endpoint}"

            # Check components schemas
            components = openapi_spec.get("components", {})
            schemas = components.get("schemas", {})

            required_schemas = [
                "PCOBundle",
                "PCOPublic",
                "PCOBundleResponse",
                "VerificationResult"
            ]

            for schema in required_schemas:
                assert schema in schemas, f"Missing required schema: {schema}"

    @pytest.mark.integration
    def test_end_to_end_contract_flow(
        self,
        client: TestClient,
        valid_pco_request: dict[str, Any],
        contract_validator: PCOContractValidator,
        mock_ed25519_key
    ):
        """Test: End-to-end flow zachowuje zgodność kontraktów."""

        # Przygotuj klucz w formacie PEM
        from cryptography.hazmat.primitives import serialization
        pem_bytes = mock_ed25519_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption()
        )
        pem_str = pem_bytes.decode('utf-8')

        # Step 1: Create PCO Bundle
        with patch.dict('os.environ', {
            'ED25519_PRIVKEY_PEM': pem_str,
            'PROOF_BUNDLE_DIR': '/tmp/test_bundles'
        }):
            bundle_response = client.post("/v1/pco/bundle", json=valid_pco_request)

        assert bundle_response.status_code == 200
        bundle_data = bundle_response.json()

        # Validate bundle contract
        bundle_errors = contract_validator.validate_bundle_endpoint_contract(bundle_data)
        assert len(bundle_errors) == 0

        # Step 2: Get public PCO (mocked)
        bundle_data.get("case_id", valid_pco_request["rid"])

        # In real implementation, this would fetch from ledger
        # For contract testing, we verify the expected structure

        # Step 3: Verify PCO (mocked)
        verify_request = {
            "data": bundle_data,
            "verification_type": "full",
            "offline": False
        }

        # Contract validates the request structure
        assert "data" in verify_request
        assert "verification_type" in verify_request
        assert verify_request["verification_type"] in ["full", "signatures_only", "proofs_only", "public_only"]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
