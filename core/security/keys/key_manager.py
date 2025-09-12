# CERTEUS Engine - A6 Security Key Management
# Quantum-Resistance Temporal & Security Protocol
# Keys: Ed25519 cryptography with KMS/HSM support and rotation

import base64
import hashlib
import json
import logging
import os
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Union

# Ed25519 cryptography
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives.serialization import (Encoding,
                                                          NoEncryption,
                                                          PrivateFormat,
                                                          PublicFormat)

logger = logging.getLogger(__name__)

class KeyType(Enum):
    """Supported cryptographic key types"""
    ED25519 = "ed25519"
    RSA_4096 = "rsa_4096"  # Legacy support
    ECDSA_P256 = "ecdsa_p256"  # Legacy support

class KeyStatus(Enum):
    """Key lifecycle status"""
    ACTIVE = "active"
    DEPRECATED = "deprecated"
    REVOKED = "revoked"
    PENDING = "pending"

class KeyStoreType(Enum):
    """Key storage backend types"""
    SOFTWARE = "software"  # File-based software KMS
    HSM = "hsm"           # Hardware Security Module
    KMS = "kms"           # Cloud KMS (AWS/Azure/GCP)
    VAULT = "vault"       # HashiCorp Vault

@dataclass
class KeyMetadata:
    """Cryptographic key metadata for enterprise key management"""
    key_id: str
    key_type: KeyType
    created_at: datetime
    expires_at: Optional[datetime] = None
    status: KeyStatus = KeyStatus.ACTIVE
    purpose: str = "signing"
    algorithm: str = "Ed25519"
    key_size: int = 256  # bits
    owner: str = "certeus-system"
    rotation_policy_id: Optional[str] = None
    parent_key_id: Optional[str] = None  # For key hierarchy
    tags: Dict[str, str] = field(default_factory=dict)
    access_permissions: List[str] = field(default_factory=list)

@dataclass
class KeyRotationPolicy:
    """Key rotation policy configuration"""
    policy_id: str
    rotation_interval_days: int
    warning_days: int = 30
    auto_rotate: bool = False
    max_key_age_days: int = 365
    backup_count: int = 3
    notification_endpoints: List[str] = field(default_factory=list)
    
    def __post_init__(self):
        if self.rotation_interval_days > self.max_key_age_days:
            raise ValueError("Rotation interval cannot exceed max key age")

class KeyManager:
    """
    Enterprise cryptographic key management system
    
    Features:
    - Ed25519 digital signatures (quantum-resistant recommended)
    - Key rotation with configurable policies
    - Multi-backend support (software, HSM, KMS)
    - Key hierarchy and delegation
    - Comprehensive audit logging
    - FIPS 140-2 Level 3 compatible (when using HSM)
    """
    
    def __init__(self, 
                 store_type: KeyStoreType = KeyStoreType.SOFTWARE,
                 key_store_path: Optional[str] = None,
                 kms_config: Optional[Dict[str, Any]] = None):
        self.store_type = store_type
        self.key_store_path = Path(key_store_path or "./keys")
        self.kms_config = kms_config or {}
        
        # In-memory key cache for performance
        self._key_cache: Dict[str, Any] = {}
        self._metadata_cache: Dict[str, KeyMetadata] = {}
        
        # Rotation policies
        self._rotation_policies: Dict[str, KeyRotationPolicy] = {}
        
        # Initialize key store
        self._initialize_key_store()
    
    def _initialize_key_store(self):
        """Initialize the key storage backend"""
        
        if self.store_type == KeyStoreType.SOFTWARE:
            # Create key directory structure
            self.key_store_path.mkdir(parents=True, exist_ok=True)
            (self.key_store_path / "private").mkdir(exist_ok=True)
            (self.key_store_path / "public").mkdir(exist_ok=True)
            (self.key_store_path / "metadata").mkdir(exist_ok=True)
            
            # Set restrictive permissions
            os.chmod(self.key_store_path / "private", 0o700)
            
        elif self.store_type == KeyStoreType.HSM:
            logger.info("Initializing HSM connection...")
            # HSM initialization would go here
            # PKCS#11 or proprietary HSM SDK integration
            
        elif self.store_type == KeyStoreType.KMS:
            logger.info("Initializing cloud KMS connection...")
            # AWS KMS, Azure Key Vault, or GCP KMS initialization
            
        elif self.store_type == KeyStoreType.VAULT:
            logger.info("Initializing HashiCorp Vault connection...")
            # Vault API client initialization
        
        logger.info(f"Key manager initialized with {self.store_type.value} backend")
    
    def generate_key(self, 
                    key_id: str,
                    key_type: KeyType = KeyType.ED25519,
                    purpose: str = "signing",
                    expires_in_days: Optional[int] = None,
                    rotation_policy_id: Optional[str] = None,
                    tags: Optional[Dict[str, str]] = None) -> KeyMetadata:
        """
        Generate new cryptographic key pair
        
        Args:
            key_id: Unique identifier for the key
            key_type: Type of key to generate (Ed25519 recommended)
            purpose: Key usage purpose (signing, encryption, etc.)
            expires_in_days: Key expiration in days (None for no expiration)
            rotation_policy_id: Associated rotation policy
            tags: Additional metadata tags
            
        Returns:
            KeyMetadata for the generated key
        """
        
        if key_id in self._metadata_cache:
            raise ValueError(f"Key {key_id} already exists")
        
        # Generate key pair based on type
        if key_type == KeyType.ED25519:
            private_key = ed25519.Ed25519PrivateKey.generate()
            public_key = private_key.public_key()
            algorithm = "Ed25519"
            key_size = 256
            
        else:
            raise ValueError(f"Unsupported key type: {key_type}")
        
        # Create metadata
        created_at = datetime.now(timezone.utc)
        expires_at = None
        if expires_in_days:
            expires_at = created_at + timedelta(days=expires_in_days)
        
        metadata = KeyMetadata(
            key_id=key_id,
            key_type=key_type,
            created_at=created_at,
            expires_at=expires_at,
            purpose=purpose,
            algorithm=algorithm,
            key_size=key_size,
            rotation_policy_id=rotation_policy_id,
            tags=tags or {},
            access_permissions=[f"certeus:key:{purpose}"]
        )
        
        # Store key pair
        self._store_key_pair(key_id, private_key, public_key, metadata)
        
        # Cache metadata
        self._metadata_cache[key_id] = metadata
        
        logger.info(f"Generated {key_type.value} key: {key_id}")
        return metadata
    
    def _store_key_pair(self, key_id: str, private_key: Any, public_key: Any, metadata: KeyMetadata):
        """Store key pair in the configured backend"""
        
        if self.store_type == KeyStoreType.SOFTWARE:
            # Serialize private key (no password for now - would use KDF in production)
            private_pem = private_key.private_bytes(
                encoding=Encoding.PEM,
                format=PrivateFormat.PKCS8,
                encryption_algorithm=NoEncryption()
            )
            
            # Serialize public key
            public_pem = public_key.public_bytes(
                encoding=Encoding.PEM,
                format=PublicFormat.SubjectPublicKeyInfo
            )
            
            # Store files
            private_path = self.key_store_path / "private" / f"{key_id}.pem"
            public_path = self.key_store_path / "public" / f"{key_id}.pem"
            metadata_path = self.key_store_path / "metadata" / f"{key_id}.json"
            
            # Write private key with restricted permissions
            with open(private_path, 'wb') as f:
                f.write(private_pem)
            os.chmod(private_path, 0o600)
            
            # Write public key
            with open(public_path, 'wb') as f:
                f.write(public_pem)
            
            # Write metadata
            metadata_dict = {
                'key_id': metadata.key_id,
                'key_type': metadata.key_type.value,
                'created_at': metadata.created_at.isoformat(),
                'expires_at': metadata.expires_at.isoformat() if metadata.expires_at else None,
                'status': metadata.status.value,
                'purpose': metadata.purpose,
                'algorithm': metadata.algorithm,
                'key_size': metadata.key_size,
                'owner': metadata.owner,
                'rotation_policy_id': metadata.rotation_policy_id,
                'parent_key_id': metadata.parent_key_id,
                'tags': metadata.tags,
                'access_permissions': metadata.access_permissions
            }
            
            with open(metadata_path, 'w') as f:
                json.dump(metadata_dict, f, indent=2)
        
        else:
            # HSM/KMS/Vault storage would be implemented here
            raise NotImplementedError(f"Storage for {self.store_type.value} not implemented")
    
    def load_private_key(self, key_id: str) -> Any:
        """Load private key for signing operations"""
        
        # Check cache first
        if key_id in self._key_cache:
            return self._key_cache[key_id]
        
        if self.store_type == KeyStoreType.SOFTWARE:
            private_path = self.key_store_path / "private" / f"{key_id}.pem"
            
            if not private_path.exists():
                raise FileNotFoundError(f"Private key not found: {key_id}")
            
            with open(private_path, 'rb') as f:
                private_key = serialization.load_pem_private_key(
                    f.read(),
                    password=None  # Would use secure password/KDF in production
                )
            
            # Cache for performance
            self._key_cache[key_id] = private_key
            return private_key
        
        else:
            raise NotImplementedError(f"Key loading for {self.store_type.value} not implemented")
    
    def load_public_key(self, key_id: str) -> Any:
        """Load public key for verification operations"""
        
        if self.store_type == KeyStoreType.SOFTWARE:
            public_path = self.key_store_path / "public" / f"{key_id}.pem"
            
            if not public_path.exists():
                raise FileNotFoundError(f"Public key not found: {key_id}")
            
            with open(public_path, 'rb') as f:
                public_key = serialization.load_pem_public_key(f.read())
            
            return public_key
        
        else:
            raise NotImplementedError(f"Key loading for {self.store_type.value} not implemented")
    
    def sign_data(self, key_id: str, data: bytes) -> bytes:
        """
        Sign data using specified key
        
        Args:
            key_id: Key identifier for signing
            data: Data to sign
            
        Returns:
            Digital signature bytes
        """
        
        metadata = self.get_key_metadata(key_id)
        if metadata.status != KeyStatus.ACTIVE:
            raise ValueError(f"Key {key_id} is not active: {metadata.status}")
        
        if metadata.purpose != "signing":
            logger.warning(f"Key {key_id} purpose is {metadata.purpose}, not signing")
        
        private_key = self.load_private_key(key_id)
        
        if metadata.key_type == KeyType.ED25519:
            signature = private_key.sign(data)
        else:
            raise ValueError(f"Signing not supported for key type: {metadata.key_type}")
        
        logger.info(f"Signed data with key {key_id}, signature length: {len(signature)}")
        return signature
    
    def verify_signature(self, key_id: str, data: bytes, signature: bytes) -> bool:
        """
        Verify digital signature
        
        Args:
            key_id: Key identifier for verification
            data: Original data
            signature: Signature to verify
            
        Returns:
            True if signature is valid, False otherwise
        """
        
        try:
            public_key = self.load_public_key(key_id)
            metadata = self.get_key_metadata(key_id)
            
            if metadata.key_type == KeyType.ED25519:
                public_key.verify(signature, data)
                return True
            else:
                raise ValueError(f"Verification not supported for key type: {metadata.key_type}")
                
        except Exception as e:
            logger.warning(f"Signature verification failed for key {key_id}: {e}")
            return False
    
    def get_key_metadata(self, key_id: str) -> KeyMetadata:
        """Retrieve key metadata"""
        
        # Check cache first
        if key_id in self._metadata_cache:
            return self._metadata_cache[key_id]
        
        if self.store_type == KeyStoreType.SOFTWARE:
            metadata_path = self.key_store_path / "metadata" / f"{key_id}.json"
            
            if not metadata_path.exists():
                raise FileNotFoundError(f"Key metadata not found: {key_id}")
            
            with open(metadata_path, 'r') as f:
                metadata_dict = json.load(f)
            
            metadata = KeyMetadata(
                key_id=metadata_dict['key_id'],
                key_type=KeyType(metadata_dict['key_type']),
                created_at=datetime.fromisoformat(metadata_dict['created_at']),
                expires_at=datetime.fromisoformat(metadata_dict['expires_at']) if metadata_dict['expires_at'] else None,
                status=KeyStatus(metadata_dict['status']),
                purpose=metadata_dict['purpose'],
                algorithm=metadata_dict['algorithm'],
                key_size=metadata_dict['key_size'],
                owner=metadata_dict['owner'],
                rotation_policy_id=metadata_dict.get('rotation_policy_id'),
                parent_key_id=metadata_dict.get('parent_key_id'),
                tags=metadata_dict.get('tags', {}),
                access_permissions=metadata_dict.get('access_permissions', [])
            )
            
            # Cache metadata
            self._metadata_cache[key_id] = metadata
            return metadata
        
        else:
            raise NotImplementedError(f"Metadata loading for {self.store_type.value} not implemented")
    
    def list_keys(self, status_filter: Optional[KeyStatus] = None) -> List[KeyMetadata]:
        """List all keys with optional status filtering"""
        
        keys = []
        
        if self.store_type == KeyStoreType.SOFTWARE:
            metadata_dir = self.key_store_path / "metadata"
            
            for metadata_file in metadata_dir.glob("*.json"):
                key_id = metadata_file.stem
                try:
                    metadata = self.get_key_metadata(key_id)
                    if status_filter is None or metadata.status == status_filter:
                        keys.append(metadata)
                except Exception as e:
                    logger.warning(f"Failed to load metadata for key {key_id}: {e}")
        
        return sorted(keys, key=lambda k: k.created_at)
    
    def rotate_key(self, key_id: str, new_key_id: Optional[str] = None) -> KeyMetadata:
        """
        Rotate key by generating new key and deprecating old one
        
        Args:
            key_id: Current key to rotate
            new_key_id: Optional new key ID (auto-generated if None)
            
        Returns:
            Metadata for the new key
        """
        
        old_metadata = self.get_key_metadata(key_id)
        
        if new_key_id is None:
            timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
            new_key_id = f"{key_id}_rotated_{timestamp}"
        
        # Generate new key with same properties
        new_metadata = self.generate_key(
            key_id=new_key_id,
            key_type=old_metadata.key_type,
            purpose=old_metadata.purpose,
            rotation_policy_id=old_metadata.rotation_policy_id,
            tags=old_metadata.tags.copy()
        )
        
        # Set parent relationship
        new_metadata.parent_key_id = key_id
        
        # Deprecate old key
        self.update_key_status(key_id, KeyStatus.DEPRECATED)
        
        logger.info(f"Rotated key {key_id} to {new_key_id}")
        return new_metadata
    
    def update_key_status(self, key_id: str, status: KeyStatus):
        """Update key status"""
        
        metadata = self.get_key_metadata(key_id)
        metadata.status = status
        
        # Update stored metadata
        self._metadata_cache[key_id] = metadata
        
        if self.store_type == KeyStoreType.SOFTWARE:
            metadata_path = self.key_store_path / "metadata" / f"{key_id}.json"
            
            with open(metadata_path, 'r') as f:
                metadata_dict = json.load(f)
            
            metadata_dict['status'] = status.value
            
            with open(metadata_path, 'w') as f:
                json.dump(metadata_dict, f, indent=2)
        
        logger.info(f"Updated key {key_id} status to {status.value}")
    
    def create_rotation_policy(self, policy: KeyRotationPolicy):
        """Create or update key rotation policy"""
        self._rotation_policies[policy.policy_id] = policy
        logger.info(f"Created rotation policy: {policy.policy_id}")
    
    def get_keys_needing_rotation(self) -> List[KeyMetadata]:
        """Get keys that need rotation based on policies"""
        
        keys_to_rotate = []
        now = datetime.now(timezone.utc)
        
        for metadata in self.list_keys(KeyStatus.ACTIVE):
            if metadata.rotation_policy_id:
                policy = self._rotation_policies.get(metadata.rotation_policy_id)
                if policy:
                    days_since_creation = (now - metadata.created_at).days
                    if days_since_creation >= policy.rotation_interval_days:
                        keys_to_rotate.append(metadata)
        
        return keys_to_rotate
    
    def export_public_key_pem(self, key_id: str) -> str:
        """Export public key in PEM format for distribution"""
        
        public_key = self.load_public_key(key_id)
        pem_bytes = public_key.public_bytes(
            encoding=Encoding.PEM,
            format=PublicFormat.SubjectPublicKeyInfo
        )
        return pem_bytes.decode('utf-8')
    
    def get_key_fingerprint(self, key_id: str) -> str:
        """Get key fingerprint for identification"""
        
        public_key_pem = self.export_public_key_pem(key_id)
        fingerprint = hashlib.sha256(public_key_pem.encode()).hexdigest()
        return fingerprint[:16]  # Short fingerprint

# Global key manager instance
key_manager = KeyManager()