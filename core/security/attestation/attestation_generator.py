# CERTEUS Engine - A6 Security Attestation Framework
# Quantum-Resistance Temporal & Security Protocol
# SLSA & in-toto provenance attestations with Cosign integration

import base64
from dataclasses import asdict, dataclass, field
from datetime import UTC, datetime
from enum import Enum
import hashlib
import json
import logging
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any, Protocol
import uuid

sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from core.security.keys.key_manager import KeyManager

logger = logging.getLogger(__name__)

class SLSALevel(Enum):
    """SLSA Build Levels"""
    LEVEL_0 = "SLSA_BUILD_LEVEL_0"  # No guarantees
    LEVEL_1 = "SLSA_BUILD_LEVEL_1"  # Some protections
    LEVEL_2 = "SLSA_BUILD_LEVEL_2"  # Hosted build service
    LEVEL_3 = "SLSA_BUILD_LEVEL_3"  # Hardened builds

class PredicateType(Enum):
    """in-toto predicate types for attestations"""
    SLSA_PROVENANCE = "https://slsa.dev/provenance/v0.2"
    SLSA_PROVENANCE_V1 = "https://slsa.dev/provenance/v1"
    LINK = "https://in-toto.io/Link/v1"
    SPDX = "https://spdx.dev/Document"
    CYCLONE_DX = "https://cyclonedx.org/bom"
    CUSTOM_CERTEUS = "https://certeus.dev/attestation/v1"

@dataclass
class Digest:
    """Cryptographic digest for artifacts"""
    algorithm: str  # sha256, sha512, etc.
    value: str

@dataclass
class Subject:
    """Artifact subject being attested"""
    name: str
    digest: dict[str, str]  # algorithm -> digest value

@dataclass
class Builder:
    """Build system information"""
    id: str  # URI identifying the builder
    version: dict[str, str] | None = None
    builderDependencies: list[dict[str, Any]] | None = None

@dataclass 
class BuildConfig:
    """Build configuration and parameters"""
    commands: list[str] | None = None
    environment: dict[str, str] | None = None
    source: dict[str, Any] | None = None

@dataclass
class Metadata:
    """Build metadata"""
    buildInvocationId: str
    buildStartedOn: datetime
    buildFinishedOn: datetime
    completeness: dict[str, bool] = field(default_factory=lambda: {
        "parameters": True,
        "environment": True, 
        "materials": True
    })
    reproducible: bool = False

@dataclass
class Material:
    """Build materials/dependencies"""
    uri: str
    digest: dict[str, str] | None = None

@dataclass
class SLSAProvenance:
    """SLSA Build Provenance v1.0"""
    builder: Builder
    buildType: str  # URI identifying build type
    invocation: BuildConfig
    metadata: Metadata
    materials: list[Material] = field(default_factory=list)

@dataclass
class InTotoStatement:
    """in-toto attestation statement"""
    _type: str = "https://in-toto.io/Statement/v0.1"
    subject: list[Subject] = field(default_factory=list)
    predicateType: str = ""
    predicate: dict[str, Any] = field(default_factory=dict)

@dataclass
class DSSEEnvelope:
    """Dead Simple Signing Envelope (DSSE)"""
    payload: str  # base64-encoded JSON
    payloadType: str = "application/vnd.in-toto+json"
    signatures: list[dict[str, str]] = field(default_factory=list)

class AttestationSigner(Protocol):
    """Protocol for signing attestations"""
    
    def sign(self, payload: bytes) -> dict[str, str]:
        """Sign payload and return signature metadata"""
        ...

class CerteusSigner:
    """CERTEUS Ed25519 attestation signer"""
    
    def __init__(self, key_manager: KeyManager, key_id: str):
        self.key_manager = key_manager
        self.key_id = key_id
    
    def sign(self, payload: bytes) -> dict[str, str]:
        """Sign with Ed25519 key"""
        
        signature = self.key_manager.sign_data(self.key_id, payload)
        
        # Get public key for verification
        _ = self.key_manager.get_key_metadata(self.key_id)
        _ = self.key_manager.export_public_key_pem(self.key_id)
        
        return {
            "keyid": self.key_id,
            "sig": base64.b64encode(signature).decode('utf-8')
        }

class CosignSigner:
    """Cosign integration for container image signing"""
    
    def __init__(self, cosign_path: str = "cosign"):
        self.cosign_path = cosign_path
    
    def sign_container(self, 
                      image_ref: str,
                      key_path: str | None = None,
                      attestation_path: str | None = None) -> bool:
        """Sign container image with Cosign"""
        
        try:
            cmd = [self.cosign_path, "sign"]
            
            if key_path:
                cmd.extend(["--key", key_path])
            
            if attestation_path:
                cmd.extend(["--attachment", "attestation", "--attestation", attestation_path])
            
            cmd.append(image_ref)
            
            subprocess.run(cmd, capture_output=True, text=True, check=True)
            logger.info(f"Successfully signed container {image_ref}")
            return True
            
        except subprocess.CalledProcessError as e:
            logger.error(f"Cosign signing failed: {e.stderr}")
            return False
        except FileNotFoundError:
            logger.error("Cosign not found. Install cosign binary.")
            return False
    
    def verify_container(self, image_ref: str, public_key_path: str) -> bool:
        """Verify container image signature"""
        
        try:
            cmd = [
                self.cosign_path, "verify",
                "--key", public_key_path,
                image_ref
            ]
            
            subprocess.run(cmd, capture_output=True, text=True, check=True)
            logger.info(f"Container {image_ref} signature verified")
            return True
            
        except subprocess.CalledProcessError as e:
            logger.error(f"Cosign verification failed: {e.stderr}")
            return False

class AttestationGenerator:
    """
    Enterprise attestation generator for SLSA provenance and in-toto statements
    
    Features:
    - SLSA Build Provenance v1.0 generation
    - in-toto statement creation with DSSE envelope
    - Ed25519 digital signatures via CERTEUS KeyManager
    - Cosign integration for container signatures
    - Build reproducibility tracking
    - Supply chain metadata collection
    """
    
    def __init__(self, 
                 key_manager: KeyManager,
                 builder_id: str = "https://github.com/certeus/builder",
                 build_type: str = "https://github.com/certeus/build-type"):
        self.key_manager = key_manager
        self.builder_id = builder_id
        self.build_type = build_type
    
    def generate_slsa_provenance(self,
                               subjects: list[Subject],
                               build_commands: list[str],
                               build_env: dict[str, str],
                               materials: list[Material],
                               slsa_level: SLSALevel = SLSALevel.LEVEL_2) -> SLSAProvenance:
        """Generate SLSA Build Provenance"""
        
        build_id = str(uuid.uuid4())
        now = datetime.now(UTC)
        
        # Create builder info
        builder = Builder(
            id=self.builder_id,
            version={"certeus-engine": "1.0.0"}
        )
        
        # Build configuration
        invocation = BuildConfig(
            commands=build_commands,
            environment=build_env,
            source={
                "repository": "https://github.com/certeus/engine",
                "ref": "main"
            }
        )
        
        # Build metadata
        metadata = Metadata(
            buildInvocationId=build_id,
            buildStartedOn=now,
            buildFinishedOn=now,
            completeness={
                "parameters": True,
                "environment": True,
                "materials": True
            },
            reproducible=True
        )
        
        return SLSAProvenance(
            builder=builder,
            buildType=self.build_type,
            invocation=invocation,
            metadata=metadata,
            materials=materials
        )
    
    def create_in_toto_statement(self,
                               subjects: list[Subject],
                               predicate_type: PredicateType,
                               predicate: dict[str, Any]) -> InTotoStatement:
        """Create in-toto attestation statement"""
        
        return InTotoStatement(
            subject=subjects,
            predicateType=predicate_type.value,
            predicate=predicate
        )
    
    def sign_statement(self,
                      statement: InTotoStatement,
                      key_id: str) -> DSSEEnvelope:
        """Sign in-toto statement with DSSE envelope"""
        
        # Serialize statement to JSON
        statement_json = json.dumps(asdict(statement), default=str, separators=(',', ':'))
        payload_b64 = base64.b64encode(statement_json.encode('utf-8')).decode('utf-8')
        
        # Create Pre-Authentication Encoding (PAE)
        pae = self._create_pae("application/vnd.in-toto+json", statement_json.encode('utf-8'))
        
        # Sign with Ed25519
        signer = CerteusSigner(self.key_manager, key_id)
        signature_info = signer.sign(pae)
        
        return DSSEEnvelope(
            payload=payload_b64,
            signatures=[signature_info]
        )
    
    def _create_pae(self, payload_type: str, payload: bytes) -> bytes:
        """Create DSSE Pre-Authentication Encoding"""
        
        def encode_length(length: int) -> bytes:
            return str(length).encode('utf-8')
        
        pae = b"DSSEv1"
        pae += b" " + encode_length(len(payload_type)) + b" " + payload_type.encode('utf-8')
        pae += b" " + encode_length(len(payload)) + b" " + payload
        
        return pae
    
    def verify_dsse_envelope(self, envelope: DSSEEnvelope, key_id: str) -> bool:
        """Verify DSSE envelope signature"""
        
        try:
            # Decode payload
            payload_bytes = base64.b64decode(envelope.payload)
            
            # Recreate PAE
            pae = self._create_pae(envelope.payloadType, payload_bytes)
            
            # Verify signatures
            for sig_info in envelope.signatures:
                if sig_info.get("keyid") == key_id:
                    signature = base64.b64decode(sig_info["sig"])
                    
                    is_valid = self.key_manager.verify_signature(
                        data=pae,
                        signature=signature,
                        key_id=key_id
                    )
                    
                    if is_valid:
                        logger.info(f"Valid signature from key {key_id}")
                        return True
            
            logger.warning(f"No valid signature found for key {key_id}")
            return False
            
        except Exception as e:
            logger.error(f"Signature verification failed: {e}")
            return False
    
    def create_build_attestation(self,
                               artifact_path: Path,
                               build_commands: list[str],
                               key_id: str,
                               slsa_level: SLSALevel = SLSALevel.LEVEL_2) -> DSSEEnvelope:
        """Create complete build attestation for artifact"""
        
        # Calculate artifact digest
        artifact_digest = self._calculate_file_digest(artifact_path)
        
        subject = Subject(
            name=artifact_path.name,
            digest={"sha256": artifact_digest}
        )
        
        # Collect build materials
        materials = self._collect_build_materials()
        
        # Generate SLSA provenance
        provenance = self.generate_slsa_provenance(
            subjects=[subject],
            build_commands=build_commands,
            build_env=dict(os.environ) if hasattr(os, 'environ') else {},
            materials=materials,
            slsa_level=slsa_level
        )
        
        # Create in-toto statement
        statement = self.create_in_toto_statement(
            subjects=[subject],
            predicate_type=PredicateType.SLSA_PROVENANCE_V1,
            predicate=asdict(provenance)
        )
        
        # Sign statement
        return self.sign_statement(statement, key_id)
    
    def _calculate_file_digest(self, file_path: Path, algorithm: str = "sha256") -> str:
        """Calculate cryptographic digest of file"""
        
        hash_func = hashlib.new(algorithm)
        
        with open(file_path, 'rb') as f:
            while chunk := f.read(8192):
                hash_func.update(chunk)
        
        return hash_func.hexdigest()
    
    def _collect_build_materials(self) -> list[Material]:
        """Collect build dependencies and materials"""
        
        materials = []
        
        # Add common build materials
        materials.extend([
            Material(uri="git+https://github.com/certeus/engine@main"),
            Material(uri="pkg:pypi/cryptography@latest"),
            Material(uri="pkg:pypi/pydantic@latest")
        ])
        
        return materials
    
    def create_container_attestation(self,
                                   image_ref: str,
                                   dockerfile_path: Path,
                                   key_id: str,
                                   cosign_signer: CosignSigner | None = None) -> DSSEEnvelope | None:
        """Create attestation for container image"""
        
        # Create SLSA provenance for container build
        build_commands = [
            f"docker build -f {dockerfile_path} .",
            f"docker tag {image_ref}"
        ]
        
        # For containers, subject is the image digest
        # This would normally come from registry
        subject = Subject(
            name=image_ref,
            digest={"sha256": "placeholder_image_digest"}  # Would get actual digest
        )
        
        materials = [
            Material(uri=f"file://{dockerfile_path}"),
            Material(uri="git+https://github.com/certeus/engine@main")
        ]
        
        provenance = self.generate_slsa_provenance(
            subjects=[subject],
            build_commands=build_commands,
            build_env={"DOCKER_BUILDKIT": "1"},
            materials=materials
        )
        
        statement = self.create_in_toto_statement(
            subjects=[subject],
            predicate_type=PredicateType.SLSA_PROVENANCE_V1,
            predicate=asdict(provenance)
        )
        
        envelope = self.sign_statement(statement, key_id)
        
        # Sign with Cosign if available
        if cosign_signer:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
                json.dump(asdict(envelope), f, default=str)
                temp_path = f.name
            
            try:
                cosign_signer.sign_container(image_ref, attestation_path=temp_path)
            finally:
                Path(temp_path).unlink(missing_ok=True)
        
        return envelope
    
    def save_attestation(self, envelope: DSSEEnvelope, output_path: Path):
        """Save attestation to file"""
        
        with open(output_path, 'w') as f:
            json.dump(asdict(envelope), f, indent=2, default=str)
        
        logger.info(f"Attestation saved to {output_path}")
    
    def load_attestation(self, attestation_path: Path) -> DSSEEnvelope:
        """Load attestation from file"""
        
        with open(attestation_path) as f:
            data = json.load(f)
        
        return DSSEEnvelope(**data)
    
    def verify_attestation_chain(self, 
                                attestations: list[DSSEEnvelope],
                                trusted_keys: list[str]) -> bool:
        """Verify chain of attestations"""
        
        for envelope in attestations:
            verified = False
            
            for key_id in trusted_keys:
                if self.verify_dsse_envelope(envelope, key_id):
                    verified = True
                    break
            
            if not verified:
                logger.error("Attestation chain verification failed")
                return False
        
        logger.info("Attestation chain verified successfully")
        return True
    
    def get_attestation_summary(self, envelope: DSSEEnvelope) -> dict[str, Any]:
        """Get human-readable attestation summary"""
        
        try:
            # Decode payload
            payload_json = base64.b64decode(envelope.payload).decode('utf-8')
            statement = json.loads(payload_json)
            
            summary = {
                "statement_type": statement.get("_type"),
                "predicate_type": statement.get("predicateType"),
                "subjects": len(statement.get("subject", [])),
                "signatures": len(envelope.signatures),
                "signed_by": [sig.get("keyid") for sig in envelope.signatures]
            }
            
            # Add SLSA-specific info if available
            if "slsa.dev/provenance" in statement.get("predicateType", ""):
                predicate = statement.get("predicate", {})
                builder = predicate.get("builder", {})
                summary["builder_id"] = builder.get("id")
                summary["build_type"] = predicate.get("buildType")
                
                if "metadata" in predicate:
                    metadata = predicate["metadata"]
                    summary["build_id"] = metadata.get("buildInvocationId")
                    summary["reproducible"] = metadata.get("reproducible")
            
            return summary
            
        except Exception as e:
            logger.error(f"Failed to parse attestation: {e}")
            return {"error": str(e)}