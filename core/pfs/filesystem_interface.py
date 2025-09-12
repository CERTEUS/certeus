#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: core/pfs/filesystem_interface.py                    |
# | ROLE: A3 - PFS Read-Only Interface & Abstractions        |
# | PLIK: core/pfs/filesystem_interface.py                    |
# | ROLA: A3 - PFS Read-Only Interface & Abstractions        |
# +-------------------------------------------------------------+

"""
PL: A3 PFS Read-Only - interfejs systemu plików tylko do odczytu
EN: A3 PFS Read-Only - read-only filesystem interface

Provides abstract interfaces for cross-platform read-only filesystem
implementations using FUSE (Linux), Dokan (Windows), and macFUSE (macOS).

Key Features:
- Cross-platform abstraction layer
- Hash-based file materialization
- Extended attributes (xattrs) support
- Immutable read-only enforcement
- Chain integrity verification
"""

import hashlib
import os
import platform
import stat
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Union

# === PLATFORM DETECTION ===

class SupportedPlatform(Enum):
    """Supported platforms for PFS implementation"""
    LINUX = "linux"
    WINDOWS = "windows"
    MACOS = "darwin"

def get_current_platform() -> SupportedPlatform:
    """Detect current platform"""
    system = platform.system().lower()
    
    if system == "linux":
        return SupportedPlatform.LINUX
    elif system == "windows":
        return SupportedPlatform.WINDOWS
    elif system == "darwin":
        return SupportedPlatform.MACOS
    else:
        raise RuntimeError(f"Unsupported platform: {system}")

# === DATA STRUCTURES ===

@dataclass
class FileHash:
    """File hash with multiple algorithms for verification"""
    sha256: str
    sha512: Optional[str] = None
    blake3: Optional[str] = None
    
    def verify_content(self, content: bytes) -> bool:
        """Verify content matches stored hashes"""
        
        # Primary verification with SHA256
        computed_sha256 = hashlib.sha256(content).hexdigest()
        if computed_sha256 != self.sha256:
            return False
        
        # Secondary verification if available
        if self.sha512:
            computed_sha512 = hashlib.sha512(content).hexdigest()
            if computed_sha512 != self.sha512:
                return False
                
        # Tertiary verification if available
        if self.blake3:
            try:
                import blake3
                computed_blake3 = blake3.blake3(content).hexdigest()
                if computed_blake3 != self.blake3:
                    return False
            except ImportError:
                pass  # BLAKE3 not available, skip
        
        return True

@dataclass 
class ExtendedAttributes:
    """Extended attributes for files in PFS"""
    
    # Core PFS attributes
    pfs_hash: str = ""
    pfs_size: int = 0
    pfs_created: str = ""
    pfs_chain_position: int = 0
    pfs_bundle_id: str = ""
    pfs_case_id: str = ""
    
    # Security attributes  
    pfs_signature: str = ""
    pfs_public_key: str = ""
    pfs_tsa_timestamp: str = ""
    
    # Metadata
    pfs_mime_type: str = ""
    pfs_encoding: str = ""
    pfs_version: str = "1.0"
    
    # Custom attributes
    custom: Dict[str, str] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, str]:
        """Convert to dictionary for xattr storage"""
        result = {}
        
        # Add all pfs_ attributes
        for key, value in self.__dict__.items():
            if key.startswith("pfs_") and value:
                result[f"user.{key}"] = str(value)
        
        # Add custom attributes
        for key, value in self.custom.items():
            if not key.startswith("user."):
                key = f"user.pfs_custom_{key}"
            result[key] = str(value)
        
        return result
    
    @classmethod
    def from_dict(cls, attrs: Dict[str, str]) -> "ExtendedAttributes":
        """Create from dictionary of xattrs"""
        
        instance = cls()
        custom = {}
        
        for key, value in attrs.items():
            if key.startswith("user.pfs_"):
                attr_name = key[5:]  # Remove "user." prefix
                
                if attr_name.startswith("pfs_custom_"):
                    custom_key = attr_name[11:]  # Remove "pfs_custom_" prefix  
                    custom[custom_key] = value
                elif hasattr(instance, attr_name):
                    # Convert to appropriate type
                    current_value = getattr(instance, attr_name)
                    if isinstance(current_value, int):
                        setattr(instance, attr_name, int(value))
                    else:
                        setattr(instance, attr_name, value)
        
        instance.custom = custom
        return instance

@dataclass
class VirtualFileInfo:
    """Information about a virtual file in PFS"""
    
    path: str
    file_hash: FileHash
    size: int
    mode: int
    created_time: datetime
    modified_time: datetime
    extended_attrs: ExtendedAttributes
    
    # Materialization info
    is_materialized: bool = False
    materialized_path: Optional[str] = None
    materialization_time: Optional[datetime] = None
    
    def get_stat(self) -> os.stat_result:
        """Generate stat result for virtual file"""
        
        # Create stat-like result
        st_mode = stat.S_IFREG | (self.mode & 0o777)  # Regular file with permissions
        st_size = self.size
        st_mtime = self.modified_time.timestamp()
        st_ctime = self.created_time.timestamp()
        st_atime = st_mtime  # Access time same as modify time
        
        # Create mock stat result
        stat_result = os.stat_result((
            st_mode,    # st_mode
            0,          # st_ino (inode)
            0,          # st_dev (device)  
            1,          # st_nlink (links)
            os.getuid() if hasattr(os, 'getuid') else 0,  # st_uid
            os.getgid() if hasattr(os, 'getgid') else 0,  # st_gid
            st_size,    # st_size
            st_atime,   # st_atime
            st_mtime,   # st_mtime
            st_ctime    # st_ctime
        ))
        
        return stat_result

@dataclass
class VirtualDirectoryInfo:
    """Information about a virtual directory in PFS"""
    
    path: str
    mode: int = 0o755
    created_time: datetime = field(default_factory=datetime.now)
    modified_time: datetime = field(default_factory=datetime.now)
    
    # Directory contents
    files: Dict[str, VirtualFileInfo] = field(default_factory=dict)
    subdirectories: Dict[str, "VirtualDirectoryInfo"] = field(default_factory=dict)
    
    def get_stat(self) -> os.stat_result:
        """Generate stat result for virtual directory"""
        
        st_mode = stat.S_IFDIR | (self.mode & 0o777)  # Directory with permissions
        st_mtime = self.modified_time.timestamp()
        st_ctime = self.created_time.timestamp()
        st_atime = st_mtime
        
        stat_result = os.stat_result((
            st_mode,    # st_mode
            0,          # st_ino
            0,          # st_dev
            2,          # st_nlink (directories have at least 2 links)
            os.getuid() if hasattr(os, 'getuid') else 0,  # st_uid
            os.getgid() if hasattr(os, 'getgid') else 0,  # st_gid
            4096,       # st_size (standard directory size)
            st_atime,   # st_atime
            st_mtime,   # st_mtime
            st_ctime    # st_ctime
        ))
        
        return stat_result
    
    def list_entries(self) -> List[str]:
        """List all entries in directory"""
        entries = ["..", "."]  # Parent and current directory
        entries.extend(self.files.keys())
        entries.extend(self.subdirectories.keys())
        return entries

# === FILESYSTEM OPERATIONS ===

class FilesystemError(Exception):
    """Base exception for filesystem operations"""
    pass

class ReadOnlyViolationError(FilesystemError):
    """Raised when attempting write operations on read-only filesystem"""
    pass

class FileNotFoundError(FilesystemError):
    """Raised when file is not found in virtual filesystem"""
    pass

class MaterializationError(FilesystemError):
    """Raised when file materialization fails"""
    pass

class HashVerificationError(FilesystemError):
    """Raised when hash verification fails"""
    pass

# === ABSTRACT INTERFACES ===

class PFSFilesystemInterface(ABC):
    """Abstract interface for PFS read-only filesystem implementations"""
    
    @abstractmethod
    async def initialize(self) -> None:
        """Initialize the filesystem implementation"""
        pass
    
    @abstractmethod
    async def mount(self, mount_point: str) -> None:
        """Mount the filesystem at specified mount point"""
        pass
    
    @abstractmethod
    async def unmount(self) -> None:
        """Unmount the filesystem"""
        pass
    
    @abstractmethod
    async def is_mounted(self) -> bool:
        """Check if filesystem is currently mounted"""
        pass
    
    # === FILE OPERATIONS ===
    
    @abstractmethod
    async def getattr(self, path: str) -> os.stat_result:
        """Get file/directory attributes"""
        pass
    
    @abstractmethod
    async def readdir(self, path: str) -> List[str]:
        """Read directory contents"""
        pass
    
    @abstractmethod
    async def open(self, path: str, flags: int) -> int:
        """Open file and return file descriptor"""
        pass
    
    @abstractmethod
    async def read(self, path: str, size: int, offset: int, fh: int) -> bytes:
        """Read data from file"""
        pass
    
    @abstractmethod
    async def release(self, path: str, fh: int) -> None:
        """Release file descriptor"""
        pass
    
    # === EXTENDED ATTRIBUTES ===
    
    @abstractmethod
    async def listxattr(self, path: str) -> List[str]:
        """List extended attributes"""
        pass
    
    @abstractmethod
    async def getxattr(self, path: str, name: str) -> bytes:
        """Get extended attribute value"""
        pass
    
    # === WRITE OPERATIONS (Should fail for read-only) ===
    
    async def create(self, path: str, mode: int) -> None:
        """Create file - should fail for read-only filesystem"""
        raise ReadOnlyViolationError(f"Cannot create file {path}: filesystem is read-only")
    
    async def write(self, path: str, data: bytes, offset: int, fh: int) -> int:
        """Write data - should fail for read-only filesystem"""
        raise ReadOnlyViolationError(f"Cannot write to {path}: filesystem is read-only")
    
    async def mkdir(self, path: str, mode: int) -> None:
        """Create directory - should fail for read-only filesystem"""
        raise ReadOnlyViolationError(f"Cannot create directory {path}: filesystem is read-only")
    
    async def unlink(self, path: str) -> None:
        """Delete file - should fail for read-only filesystem"""
        raise ReadOnlyViolationError(f"Cannot delete file {path}: filesystem is read-only")
    
    async def rmdir(self, path: str) -> None:
        """Delete directory - should fail for read-only filesystem"""
        raise ReadOnlyViolationError(f"Cannot delete directory {path}: filesystem is read-only")
    
    async def setxattr(self, path: str, name: str, value: bytes, flags: int) -> None:
        """Set extended attribute - should fail for read-only filesystem"""
        raise ReadOnlyViolationError(f"Cannot set xattr {name} on {path}: filesystem is read-only")

class PFSMaterializerInterface(ABC):
    """Abstract interface for file materialization from ledger/bundles"""
    
    @abstractmethod
    async def materialize_file(self, file_info: VirtualFileInfo, target_path: str) -> bool:
        """Materialize virtual file to actual filesystem"""
        pass
    
    @abstractmethod
    async def verify_materialized_file(self, file_info: VirtualFileInfo, materialized_path: str) -> bool:
        """Verify materialized file matches expected hashes"""
        pass
    
    @abstractmethod 
    async def get_virtual_tree(self, case_id: str) -> VirtualDirectoryInfo:
        """Get virtual directory tree for a case"""
        pass
    
    @abstractmethod
    async def resolve_file_content(self, file_hash: FileHash) -> bytes:
        """Resolve file content from ledger/bundles using hash"""
        pass

class PFSCacheInterface(ABC):
    """Abstract interface for materialized file caching"""
    
    @abstractmethod
    async def get_cached_file(self, file_hash: str) -> Optional[str]:
        """Get path to cached materialized file"""
        pass
    
    @abstractmethod
    async def cache_file(self, file_hash: str, content: bytes) -> str:
        """Cache materialized file and return path"""
        pass
    
    @abstractmethod
    async def invalidate_cache(self, file_hash: Optional[str] = None) -> None:
        """Invalidate cache (specific file or all files)"""
        pass
    
    @abstractmethod
    async def get_cache_stats(self) -> Dict[str, Any]:
        """Get cache statistics"""
        pass

# === PLATFORM-SPECIFIC FACTORY ===

class PFSFilesystemFactory:
    """Factory for creating platform-specific PFS filesystem implementations"""
    
    @staticmethod
    def create_filesystem(platform: Optional[SupportedPlatform] = None) -> PFSFilesystemInterface:
        """Create platform-specific filesystem implementation"""
        
        if platform is None:
            platform = get_current_platform()
        
        if platform == SupportedPlatform.LINUX:
            from services.pfs_service.linux_fuse import LinuxFUSEFilesystem
            return LinuxFUSEFilesystem()
        elif platform == SupportedPlatform.WINDOWS:
            from services.pfs_service.windows_dokan import \
                WindowsDokanFilesystem
            return WindowsDokanFilesystem()
        elif platform == SupportedPlatform.MACOS:
            from services.pfs_service.macos_fuse import MacOSFUSEFilesystem
            return MacOSFUSEFilesystem()
        else:
            raise RuntimeError(f"Unsupported platform: {platform}")

# === CONFIGURATION ===

@dataclass
class PFSConfig:
    """Configuration for PFS read-only filesystem"""
    
    # Mount configuration
    mount_point: str = "/mnt/certeus"
    allow_other: bool = True
    auto_unmount: bool = True
    
    # Materialization configuration
    cache_dir: str = "/tmp/certeus_pfs_cache"
    max_cache_size_mb: int = 1024  # 1GB default
    cache_ttl_hours: int = 24
    
    # Performance configuration
    max_file_handles: int = 1000
    read_buffer_size: int = 64 * 1024  # 64KB
    materialization_timeout: int = 300  # 5 minutes
    
    # Security configuration
    verify_all_hashes: bool = True
    require_signatures: bool = False
    allowed_users: Set[str] = field(default_factory=set)
    
    # Platform-specific options
    platform_options: Dict[str, Any] = field(default_factory=dict)
    
    @classmethod
    def from_env(cls) -> "PFSConfig":
        """Create configuration from environment variables"""
        
        config = cls()
        
        # Mount configuration
        config.mount_point = os.getenv("PFS_MOUNT_POINT", config.mount_point)
        config.allow_other = os.getenv("PFS_ALLOW_OTHER", "true").lower() == "true"
        config.auto_unmount = os.getenv("PFS_AUTO_UNMOUNT", "true").lower() == "true"
        
        # Cache configuration
        config.cache_dir = os.getenv("PFS_CACHE_DIR", config.cache_dir)
        config.max_cache_size_mb = int(os.getenv("PFS_MAX_CACHE_SIZE_MB", config.max_cache_size_mb))
        config.cache_ttl_hours = int(os.getenv("PFS_CACHE_TTL_HOURS", config.cache_ttl_hours))
        
        # Performance configuration
        config.max_file_handles = int(os.getenv("PFS_MAX_FILE_HANDLES", config.max_file_handles))
        config.read_buffer_size = int(os.getenv("PFS_READ_BUFFER_SIZE", config.read_buffer_size))
        config.materialization_timeout = int(os.getenv("PFS_MATERIALIZATION_TIMEOUT", config.materialization_timeout))
        
        # Security configuration
        config.verify_all_hashes = os.getenv("PFS_VERIFY_ALL_HASHES", "true").lower() == "true"
        config.require_signatures = os.getenv("PFS_REQUIRE_SIGNATURES", "false").lower() == "true"
        
        allowed_users_str = os.getenv("PFS_ALLOWED_USERS", "")
        if allowed_users_str:
            config.allowed_users = set(allowed_users_str.split(","))
        
        return config

# === EXPORTS ===

__all__ = [
    # Platform detection
    "SupportedPlatform", "get_current_platform",
    
    # Data structures
    "FileHash", "ExtendedAttributes", "VirtualFileInfo", "VirtualDirectoryInfo",
    
    # Exceptions
    "FilesystemError", "ReadOnlyViolationError", "FileNotFoundError",
    "MaterializationError", "HashVerificationError",
    
    # Interfaces
    "PFSFilesystemInterface", "PFSMaterializerInterface", "PFSCacheInterface",
    
    # Factory and configuration
    "PFSFilesystemFactory", "PFSConfig"
]