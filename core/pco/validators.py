#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pco/validators.py                               |
# | ROLE: PCO Schema validators                                 |
# | PLIK: core/pco/validators.py                               |
# | ROLA: Walidatory schematów PCO                             |
# +-------------------------------------------------------------+

"""
PL: Walidatory schematów PCO v1.0 - pełny i publiczny.
EN: PCO v1.0 schema validators - full and public.
"""

from __future__ import annotations

import json
import re
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Union

import jsonschema
from jsonschema import Draft202012Validator, validators
from jsonschema.exceptions import ValidationError


class PCOValidationError(Exception):
    """Custom exception dla błędów walidacji PCO."""

    def __init__(self, message: str, errors: Optional[List[str]] = None):
        super().__init__(message)
        self.errors = errors or []


class PCOValidator:
    """Walidator dla schematu PCO v1.0."""

    def __init__(self, schema_path: Optional[Path] = None):
        if schema_path is None:
            schema_path = Path(__file__).parent.parent.parent / "schemas" / "pco.schema.json"

        self.schema_path = schema_path
        self._schema = None
        self._validator = None

    @property
    def schema(self) -> Dict[str, Any]:
        """Lazy loading schematu."""
        if self._schema is None:
            try:
                with open(self.schema_path, 'r', encoding='utf-8') as f:
                    self._schema = json.load(f)
            except FileNotFoundError:
                raise PCOValidationError(f"Schema file not found: {self.schema_path}")
            except json.JSONDecodeError as e:
                raise PCOValidationError(f"Invalid JSON in schema: {e}")
        return self._schema

    @property
    def validator(self) -> Draft202012Validator:
        """Lazy loading walidatora."""
        if self._validator is None:
            self._validator = Draft202012Validator(self.schema)
        return self._validator

    def validate(self, pco_data: Dict[str, Any], strict: bool = True) -> List[str]:
        """
        Waliduje dane PCO względem schematu.

        Args:
            pco_data: Dane PCO do walidacji
            strict: Czy używać ścisłej walidacji

        Returns:
            Lista błędów walidacji (pusta jeśli OK)

        Raises:
            PCOValidationError: W przypadku krytycznych błędów
        """
        errors = []

        try:
            # Podstawowa walidacja schematu
            schema_errors = list(self.validator.iter_errors(pco_data))
            for error in schema_errors:
                errors.append(f"Schema validation: {error.message} at {'.'.join(str(p) for p in error.absolute_path)}")

            # Dodatkowe walidacje biznesowe
            if strict:
                errors.extend(self._validate_business_rules(pco_data))

        except Exception as e:
            raise PCOValidationError(f"Validation failed: {str(e)}")

        return errors

    def _validate_business_rules(self, pco_data: Dict[str, Any]) -> List[str]:
        """Walidacja reguł biznesowych."""
        errors = []

        # Walidacja case_id format
        case_id = pco_data.get('case_id', '')
        if not re.match(r'^[A-Z]{3}-[0-9]{6}$', case_id):
            errors.append(f"Invalid case_id format: {case_id}")

        # Walidacja timestamps
        created_at = pco_data.get('created_at')
        if created_at:
            try:
                datetime.fromisoformat(created_at.replace('Z', '+00:00'))
            except ValueError:
                errors.append(f"Invalid created_at timestamp: {created_at}")

        # Walidacja podpisów
        signatures = pco_data.get('signatures', [])
        if not signatures:
            errors.append("At least one signature is required")

        for i, sig in enumerate(signatures):
            if sig.get('alg') == 'ed25519' and sig.get('signature'):
                # Sprawdź czy podpis ma właściwą długość base64
                try:
                    import base64
                    decoded = base64.urlsafe_b64decode(sig['signature'] + '==')
                    if len(decoded) != 64:  # Ed25519 signature length
                        errors.append(f"Invalid Ed25519 signature length in signature {i}")
                except Exception:
                    errors.append(f"Invalid base64 signature format in signature {i}")

        # Walidacja merkle_root
        ledger = pco_data.get('ledger', {})
        merkle_root = ledger.get('merkle_root', '')
        if merkle_root and not re.match(r'^[a-f0-9]{64}$', merkle_root):
            errors.append(f"Invalid merkle_root format: {merkle_root}")

        # Walidacja digest'ów w sources
        sources = pco_data.get('sources', [])
        for i, source in enumerate(sources):
            digest = source.get('digest', '')
            if not digest.startswith('sha256:') or not re.match(r'^sha256:[a-f0-9]{64}$', digest):
                errors.append(f"Invalid digest format in source {i}: {digest}")

        # Walidacja confidence w claims
        claims = pco_data.get('claims', [])
        for i, claim in enumerate(claims):
            confidence = claim.get('confidence')
            if confidence is not None and (confidence < 0 or confidence > 1):
                errors.append(f"Invalid confidence value in claim {i}: {confidence}")

        return errors

    def is_valid(self, pco_data: Dict[str, Any], strict: bool = True) -> bool:
        """Sprawdza czy dane PCO są poprawne."""
        return len(self.validate(pco_data, strict)) == 0

    def validate_file(self, file_path: Path, strict: bool = True) -> List[str]:
        """Waliduje plik PCO."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                pco_data = json.load(f)
            return self.validate(pco_data, strict)
        except Exception as e:
            return [f"Failed to load PCO file: {str(e)}"]


class PCOPublicValidator:
    """Walidator dla schematu PCO Public v1.0."""

    def __init__(self, schema_path: Optional[Path] = None):
        if schema_path is None:
            schema_path = Path(__file__).parent.parent.parent / "schemas" / "pco-public.schema.json"

        self.schema_path = schema_path
        self._schema = None
        self._validator = None

    @property
    def schema(self) -> Dict[str, Any]:
        """Lazy loading schematu."""
        if self._schema is None:
            try:
                with open(self.schema_path, 'r', encoding='utf-8') as f:
                    self._schema = json.load(f)
            except FileNotFoundError:
                raise PCOValidationError(f"Schema file not found: {self.schema_path}")
            except json.JSONDecodeError as e:
                raise PCOValidationError(f"Invalid JSON in schema: {e}")
        return self._schema

    @property
    def validator(self) -> Draft202012Validator:
        """Lazy loading walidatora."""
        if self._validator is None:
            self._validator = Draft202012Validator(self.schema)
        return self._validator

    def validate(self, pco_public_data: Dict[str, Any]) -> List[str]:
        """Waliduje dane PCO Public."""
        errors = []

        try:
            schema_errors = list(self.validator.iter_errors(pco_public_data))
            for error in schema_errors:
                errors.append(f"Schema validation: {error.message} at {'.'.join(str(p) for p in error.absolute_path)}")

            # Dodatkowe walidacje dla PCO Public
            errors.extend(self._validate_redaction_rules(pco_public_data))

        except Exception as e:
            raise PCOValidationError(f"Validation failed: {str(e)}")

        return errors

    def _validate_redaction_rules(self, pco_data: Dict[str, Any]) -> List[str]:
        """Walidacja reguł redakcji."""
        errors = []

        # Sprawdź czy redaction_info jest obecne
        redaction_info = pco_data.get('redaction_info')
        if not redaction_info:
            errors.append("redaction_info is required for public PCO")
            return errors

        # Sprawdź ETag
        etag = redaction_info.get('etag')
        if etag and not re.match(r'^"[a-f0-9]{32}"$', etag):
            errors.append(f"Invalid ETag format: {etag}")

        # Sprawdź czy nie ma wrażliwych danych w claims_summary
        claims_summary = pco_data.get('claims_summary', {})
        redacted_texts = claims_summary.get('redacted_texts', [])
        for i, text in enumerate(redacted_texts):
            summary = text.get('summary', '')
            # Podstawowe sprawdzenie PII w summary
            if any(keyword in summary.lower() for keyword in ['pesel', 'nip', 'regon', '@', 'tel:', '+48']):
                errors.append(f"Potential PII detected in redacted_text summary {i}")

        return errors

    def is_valid(self, pco_public_data: Dict[str, Any]) -> bool:
        """Sprawdza czy dane PCO Public są poprawne."""
        return len(self.validate(pco_public_data)) == 0

    def validate_file(self, file_path: Path) -> List[str]:
        """Waliduje plik PCO Public."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                pco_data = json.load(f)
            return self.validate(pco_data)
        except Exception as e:
            return [f"Failed to load PCO Public file: {str(e)}"]


class PCOContractValidator:
    """Walidator kontraktów API - sprawdza zgodność między OpenAPI a schematami."""

    def __init__(self, openapi_path: Optional[Path] = None):
        if openapi_path is None:
            openapi_path = Path(__file__).parent.parent.parent / "docs" / "api" / "openapi.yaml"

        self.openapi_path = openapi_path
        self.pco_validator = PCOValidator()
        self.pco_public_validator = PCOPublicValidator()

    def validate_bundle_endpoint_contract(self, bundle_response: Dict[str, Any]) -> List[str]:
        """Waliduje czy odpowiedź z /v1/pco/bundle jest zgodna z kontraktem."""
        errors = []

        # Sprawdź czy zawiera wszystkie wymagane pola dla backward compatibility
        required_legacy_fields = ['rid', 'smt2_hash', 'lfsc', 'signature', 'ok']
        for field in required_legacy_fields:
            if field not in bundle_response:
                errors.append(f"Missing required legacy field: {field}")

        # Waliduj jako pełny PCO jeśli zawiera schemat v1.0
        if bundle_response.get('version') == '1.0':
            errors.extend(self.pco_validator.validate(bundle_response))

        return errors

    def validate_public_endpoint_contract(self, public_response: Dict[str, Any]) -> List[str]:
        """Waliduje czy odpowiedź z /pco/public/{case_id} jest zgodna z kontraktem."""
        return self.pco_public_validator.validate(public_response)


# CLI interface
if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(description="PCO Schema Validator")
    parser.add_argument("file", help="Path to PCO JSON file")
    parser.add_argument("--type", choices=["pco", "public"], default="pco", help="PCO type")
    parser.add_argument("--strict", action="store_true", help="Enable strict validation")

    args = parser.parse_args()

    file_path = Path(args.file)
    if not file_path.exists():
        print(f"Error: File not found: {file_path}")
        sys.exit(1)

    if args.type == "pco":
        validator = PCOValidator()
        errors = validator.validate_file(file_path, strict=args.strict)
    else:
        validator = PCOPublicValidator()
        errors = validator.validate_file(file_path)

    if errors:
        print("Validation errors:")
        for error in errors:
            print(f"  - {error}")
        sys.exit(1)
    else:
        print("✓ Validation passed")
        sys.exit(0)
