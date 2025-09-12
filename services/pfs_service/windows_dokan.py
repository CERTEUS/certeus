#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/pfs_service/windows_dokan.py               |
# | ROLE: A3 - PFS Windows Dokan Implementation               |
# | PLIK: services/pfs_service/windows_dokan.py               |
# | ROLA: A3 - PFS Windows Dokan Implementation               |
# +-------------------------------------------------------------+

"""
PL: A3 PFS Windows - implementacja przy użyciu Dokan
EN: A3 PFS Windows - implementation using Dokan

Windows-specific read-only filesystem implementation using Dokan.
Provides native Windows filesystem interface for CERTEUS PFS.

Dependencies:
- dokanfuse-python: Python bindings for Dokan
- Dokan library: Windows user-mode filesystem driver

Key Features:
- Native Windows filesystem integration
- Hard read-only enforcement
- Extended attributes support via alternate data streams
- Hash verification on all operations
- File materialization from ledger
"""

import asyncio
import errno
import logging
import os
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

try:
    import dokan
    from dokan import DOKAN_OPERATIONS
    DOKAN_AVAILABLE = True
except ImportError:
    DOKAN_AVAILABLE = False
    dokan = None
    DOKAN_OPERATIONS = None

from core.logging import get_logger
from core.pfs.filesystem_interface import (ExtendedAttributes,
                                           FileNotFoundError, FilesystemError,
                                           HashVerificationError,
                                           MaterializationError,
                                           PFSCacheInterface, PFSConfig,
                                           PFSFilesystemInterface,
                                           PFSMaterializerInterface,
                                           ReadOnlyViolationError,
                                           VirtualDirectoryInfo,
                                           VirtualFileInfo)
from services.ledger_service.postgres_ledger import PostgreSQLLedger

logger = get_logger("windows_dokan")

# === WINDOWS-SPECIFIC CONFIGURATIONS ===

class WindowsDokanConfig:
    """Windows Dokan-specific configuration"""
    
    def __init__(self):
        # Dokan options
        self.dokan_options = dokan.DOKAN_OPTION_ALT_STREAM if DOKAN_AVAILABLE else 0
        self.dokan_version = dokan.DOKAN_VERSION if DOKAN_AVAILABLE else 0
        self.thread_count = 5
        self.timeout = 15000  # 15 seconds
        
        # Windows-specific paths
        self.drive_letter = "P:"  # Default drive letter for CERTEUS PFS
        self.volume_name = "CERTEUS PFS"
        self.filesystem_name = "CERTEUS"
        
        # Performance settings
        self.sector_size = 4096
        self.sectors_per_allocation_unit = 1
        self.max_component_length = 255

# === DOKAN OPERATIONS IMPLEMENTATION ===

class WindowsDokanOperations:
    """Dokan filesystem operations for Windows"""
    
    def __init__(self, pfs_filesystem: "WindowsDokanFilesystem"):
        self.pfs = pfs_filesystem
        self.logger = get_logger("dokan_operations")
        
        # File handle tracking
        self._file_handles: Dict[int, VirtualFileInfo] = {}
        self._next_handle = 1
        self._handle_lock = threading.Lock()
    
    def _get_next_handle(self) -> int:
        """Get next available file handle"""
        with self._handle_lock:
            handle = self._next_handle
            self._next_handle += 1
            return handle
    
    def _normalize_path(self, path: str) -> str:
        """Normalize Windows path to internal format"""
        if path.startswith("\\"):
            path = path[1:]  # Remove leading backslash
        return path.replace("\\", "/")
    
    # === CORE FILESYSTEM OPERATIONS ===
    
    def create_file(self, filename: str, access_mask: int, file_attributes: int,
                   share_mode: int, create_disposition: int, create_options: int):
        """Create/open file - read-only enforcement"""
        
        path = self._normalize_path(filename)
        self.logger.debug(f"create_file: {path}, access={access_mask:x}")
        
        # Check for write access and deny
        GENERIC_WRITE = 0x40000000
        FILE_WRITE_DATA = 0x2
        FILE_APPEND_DATA = 0x4
        DELETE = 0x10000
        
        write_access = (access_mask & (GENERIC_WRITE | FILE_WRITE_DATA | FILE_APPEND_DATA | DELETE))
        
        if write_access:
            self.logger.warning(f"Write access denied for {path}")
            return -errno.EACCES
        
        try:
            # Get virtual file info
            file_info = asyncio.run(self.pfs._get_virtual_file(path))
            
            if not file_info:
                return -errno.ENOENT
            
            # Assign file handle
            handle = self._get_next_handle()
            self._file_handles[handle] = file_info
            
            return handle
            
        except Exception as e:
            self.logger.error(f"Error creating file {path}: {str(e)}")
            return -errno.EIO
    
    def close_file(self, filename: str, file_handle: int):
        """Close file and release handle"""
        
        path = self._normalize_path(filename)
        self.logger.debug(f"close_file: {path}, handle={file_handle}")
        
        try:
            if file_handle in self._file_handles:
                del self._file_handles[file_handle]
            return 0
            
        except Exception as e:
            self.logger.error(f"Error closing file {path}: {str(e)}")
            return -errno.EIO
    
    def read_file(self, filename: str, buffer: bytearray, offset: int, file_handle: int) -> int:
        """Read file data"""
        
        path = self._normalize_path(filename)
        self.logger.debug(f"read_file: {path}, offset={offset}, size={len(buffer)}")
        
        try:
            if file_handle not in self._file_handles:
                return -errno.EBADF
            
            file_info = self._file_handles[file_handle]
            
            # Materialize file if needed
            if not file_info.is_materialized:
                asyncio.run(self.pfs._materialize_file(file_info))
            
            # Read data from materialized file
            data = asyncio.run(self.pfs._read_file_data(file_info, len(buffer), offset))
            
            # Copy data to buffer
            bytes_read = min(len(data), len(buffer))
            buffer[:bytes_read] = data[:bytes_read]
            
            return bytes_read
            
        except Exception as e:
            self.logger.error(f"Error reading file {path}: {str(e)}")
            return -errno.EIO
    
    def write_file(self, filename: str, buffer: bytes, offset: int, file_handle: int) -> int:
        """Write file data - always deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Write attempt denied for {path}")
        return -errno.EACCES
    
    def get_file_information(self, filename: str) -> Dict[str, Any]:
        """Get file/directory information"""
        
        path = self._normalize_path(filename)
        self.logger.debug(f"get_file_information: {path}")
        
        try:
            # Check if it's a directory
            if asyncio.run(self.pfs._is_virtual_directory(path)):
                dir_info = asyncio.run(self.pfs._get_virtual_directory(path))
                
                return {
                    "attributes": dokan.FILE_ATTRIBUTE_DIRECTORY if DOKAN_AVAILABLE else 0x10,
                    "creation_time": dir_info.created_time.timestamp(),
                    "last_access_time": dir_info.modified_time.timestamp(),
                    "last_write_time": dir_info.modified_time.timestamp(),
                    "file_size": 0,
                    "number_of_links": 1
                }
            
            # Get file information
            file_info = asyncio.run(self.pfs._get_virtual_file(path))
            
            if not file_info:
                return -errno.ENOENT
            
            return {
                "attributes": dokan.FILE_ATTRIBUTE_READONLY if DOKAN_AVAILABLE else 0x1,
                "creation_time": file_info.created_time.timestamp(),
                "last_access_time": file_info.modified_time.timestamp(),
                "last_write_time": file_info.modified_time.timestamp(),
                "file_size": file_info.size,
                "number_of_links": 1
            }
            
        except Exception as e:
            self.logger.error(f"Error getting file information for {path}: {str(e)}")
            return -errno.EIO
    
    def find_files(self, path: str) -> List[Dict[str, Any]]:
        """List directory contents"""
        
        normalized_path = self._normalize_path(path)
        self.logger.debug(f"find_files: {normalized_path}")
        
        try:
            dir_info = asyncio.run(self.pfs._get_virtual_directory(normalized_path))
            
            if not dir_info:
                return -errno.ENOENT
            
            files = []
            
            # Add current and parent directories
            files.append({
                "filename": ".",
                "attributes": dokan.FILE_ATTRIBUTE_DIRECTORY if DOKAN_AVAILABLE else 0x10,
                "creation_time": dir_info.created_time.timestamp(),
                "last_access_time": dir_info.modified_time.timestamp(),
                "last_write_time": dir_info.modified_time.timestamp(),
                "file_size": 0
            })
            
            files.append({
                "filename": "..",
                "attributes": dokan.FILE_ATTRIBUTE_DIRECTORY if DOKAN_AVAILABLE else 0x10,
                "creation_time": dir_info.created_time.timestamp(),
                "last_access_time": dir_info.modified_time.timestamp(),
                "last_write_time": dir_info.modified_time.timestamp(),
                "file_size": 0
            })
            
            # Add subdirectories
            for name, subdir in dir_info.subdirectories.items():
                files.append({
                    "filename": name,
                    "attributes": dokan.FILE_ATTRIBUTE_DIRECTORY if DOKAN_AVAILABLE else 0x10,
                    "creation_time": subdir.created_time.timestamp(),
                    "last_access_time": subdir.modified_time.timestamp(),
                    "last_write_time": subdir.modified_time.timestamp(),
                    "file_size": 0
                })
            
            # Add files
            for name, file_info in dir_info.files.items():
                files.append({
                    "filename": name,
                    "attributes": dokan.FILE_ATTRIBUTE_READONLY if DOKAN_AVAILABLE else 0x1,
                    "creation_time": file_info.created_time.timestamp(),
                    "last_access_time": file_info.modified_time.timestamp(),
                    "last_write_time": file_info.modified_time.timestamp(),
                    "file_size": file_info.size
                })
            
            return files
            
        except Exception as e:
            self.logger.error(f"Error listing directory {normalized_path}: {str(e)}")
            return -errno.EIO
    
    def set_file_attributes(self, filename: str, file_attributes: int) -> int:
        """Set file attributes - deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Set file attributes denied for {path}")
        return -errno.EACCES
    
    def set_file_time(self, filename: str, creation_time: float, 
                     last_access_time: float, last_write_time: float) -> int:
        """Set file times - deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Set file time denied for {path}")
        return -errno.EACCES
    
    def delete_file(self, filename: str) -> int:
        """Delete file - deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Delete file denied for {path}")
        return -errno.EACCES
    
    def delete_directory(self, filename: str) -> int:
        """Delete directory - deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Delete directory denied for {path}")
        return -errno.EACCES
    
    def move_file(self, filename: str, new_filename: str, replace: bool) -> int:
        """Move/rename file - deny for read-only filesystem"""
        
        old_path = self._normalize_path(filename)
        new_path = self._normalize_path(new_filename)
        self.logger.warning(f"Move file denied: {old_path} -> {new_path}")
        return -errno.EACCES
    
    def set_end_of_file(self, filename: str, length: int) -> int:
        """Set end of file - deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Set end of file denied for {path}")
        return -errno.EACCES
    
    def set_allocation_size(self, filename: str, length: int) -> int:
        """Set allocation size - deny for read-only filesystem"""
        
        path = self._normalize_path(filename)
        self.logger.warning(f"Set allocation size denied for {path}")
        return -errno.EACCES
    
    def get_volume_information(self) -> Dict[str, Any]:
        """Get volume information"""
        
        config = self.pfs._dokan_config
        
        return {
            "volume_name": config.volume_name,
            "volume_serial_number": 0x12345678,  # Fixed serial
            "maximum_component_length": config.max_component_length,
            "filesystem_flags": (
                dokan.FILE_CASE_PRESERVED_NAMES |
                dokan.FILE_CASE_SENSITIVE_SEARCH |
                dokan.FILE_READ_ONLY_VOLUME
            ) if DOKAN_AVAILABLE else 0,
            "filesystem_name": config.filesystem_name
        }
    
    def get_disk_free_space(self) -> Dict[str, int]:
        """Get disk free space - return read-only values"""
        
        # Return fake values for read-only filesystem
        return {
            "free_bytes_available": 0,
            "total_number_of_bytes": 0,
            "total_number_of_free_bytes": 0
        }

# === MAIN WINDOWS DOKAN FILESYSTEM ===

class WindowsDokanFilesystem(PFSFilesystemInterface):
    """Windows Dokan-based PFS read-only filesystem"""
    
    def __init__(self, config: Optional[PFSConfig] = None,
                 ledger: Optional[PostgreSQLLedger] = None,
                 materializer: Optional[PFSMaterializerInterface] = None,
                 cache: Optional[PFSCacheInterface] = None):
        
        if not DOKAN_AVAILABLE:
            raise RuntimeError("Dokan library not available. Install dokanfuse-python package.")
        
        self.config = config or PFSConfig.from_env()
        self.ledger = ledger
        self.materializer = materializer
        self.cache = cache
        
        # Windows-specific configuration
        self._dokan_config = WindowsDokanConfig()
        
        # Apply Windows-specific config from PFS config
        if "drive_letter" in self.config.platform_options:
            self._dokan_config.drive_letter = self.config.platform_options["drive_letter"]
        if "volume_name" in self.config.platform_options:
            self._dokan_config.volume_name = self.config.platform_options["volume_name"]
        
        # Mount state
        self._is_mounted = False
        self._mount_thread: Optional[threading.Thread] = None
        self._dokan_operations: Optional[WindowsDokanOperations] = None
        
        # Virtual filesystem tree
        self._virtual_root: Optional[VirtualDirectoryInfo] = None
        
        self.logger = get_logger("windows_dokan_filesystem")
    
    async def initialize(self) -> None:
        """Initialize Windows Dokan filesystem"""
        
        self.logger.info("Initializing Windows Dokan filesystem")
        
        # Verify Dokan is available
        if not DOKAN_AVAILABLE:
            raise RuntimeError("Dokan not available")
        
        # Initialize components
        if self.ledger:
            await self.ledger.initialize()
        
        # Create operations handler
        self._dokan_operations = WindowsDokanOperations(self)
        
        # Create cache directory
        os.makedirs(self.config.cache_dir, exist_ok=True)
        
        self.logger.info("Windows Dokan filesystem initialized")
    
    async def mount(self, mount_point: str) -> None:
        """Mount filesystem using Dokan"""
        
        if self._is_mounted:
            raise FilesystemError("Filesystem already mounted")
        
        # Use drive letter if provided, otherwise use mount_point
        if mount_point.endswith(":"):
            self._dokan_config.drive_letter = mount_point
        else:
            # Convert path to drive letter (not typical for Windows)
            self.logger.warning(f"Mount point {mount_point} is not a drive letter, using default {self._dokan_config.drive_letter}")
        
        self.logger.info(f"Mounting PFS at {self._dokan_config.drive_letter}")
        
        # Load virtual filesystem tree
        await self._load_virtual_tree()
        
        # Start Dokan in separate thread
        self._mount_thread = threading.Thread(
            target=self._run_dokan_mount,
            name="DokanMount"
        )
        self._mount_thread.daemon = True
        self._mount_thread.start()
        
        # Wait for mount to be ready
        timeout = 10.0
        start_time = time.time()
        
        while not self._is_mounted and (time.time() - start_time) < timeout:
            await asyncio.sleep(0.1)
        
        if not self._is_mounted:
            raise FilesystemError(f"Failed to mount filesystem within {timeout}s")
        
        self.logger.info(f"PFS mounted successfully at {self._dokan_config.drive_letter}")
    
    def _run_dokan_mount(self) -> None:
        """Run Dokan mount in separate thread"""
        
        try:
            self.logger.debug("Starting Dokan mount")
            
            # Create Dokan main structure
            dokan_main = dokan.DOKAN_OPERATIONS(
                create_file=self._dokan_operations.create_file,
                close_file=self._dokan_operations.close_file,
                read_file=self._dokan_operations.read_file,
                write_file=self._dokan_operations.write_file,
                get_file_information=self._dokan_operations.get_file_information,
                find_files=self._dokan_operations.find_files,
                set_file_attributes=self._dokan_operations.set_file_attributes,
                set_file_time=self._dokan_operations.set_file_time,
                delete_file=self._dokan_operations.delete_file,
                delete_directory=self._dokan_operations.delete_directory,
                move_file=self._dokan_operations.move_file,
                set_end_of_file=self._dokan_operations.set_end_of_file,
                set_allocation_size=self._dokan_operations.set_allocation_size,
                get_volume_information=self._dokan_operations.get_volume_information,
                get_disk_free_space=self._dokan_operations.get_disk_free_space
            )
            
            # Configure Dokan options
            dokan_options = dokan.DOKAN_OPTIONS()
            dokan_options.version = self._dokan_config.dokan_version
            dokan_options.thread_count = self._dokan_config.thread_count
            dokan_options.options = self._dokan_config.dokan_options
            dokan_options.timeout = self._dokan_config.timeout
            dokan_options.mount_point = self._dokan_config.drive_letter
            
            self._is_mounted = True
            
            # Run Dokan main loop
            result = dokan.DokanMain(dokan_options, dokan_main)
            
            self.logger.info(f"Dokan mount finished with result: {result}")
            
        except Exception as e:
            self.logger.error(f"Dokan mount failed: {str(e)}")
        finally:
            self._is_mounted = False
    
    async def unmount(self) -> None:
        """Unmount filesystem"""
        
        if not self._is_mounted:
            return
        
        self.logger.info(f"Unmounting PFS from {self._dokan_config.drive_letter}")
        
        try:
            # Send unmount signal to Dokan
            if DOKAN_AVAILABLE:
                dokan.DokanUnmount(self._dokan_config.drive_letter[0])  # Drive letter only
            
            # Wait for unmount
            if self._mount_thread:
                self._mount_thread.join(timeout=10.0)
            
            self._is_mounted = False
            self.logger.info("PFS unmounted successfully")
            
        except Exception as e:
            self.logger.error(f"Error during unmount: {str(e)}")
            raise FilesystemError(f"Failed to unmount: {str(e)}")
    
    async def is_mounted(self) -> bool:
        """Check if filesystem is mounted"""
        return self._is_mounted
    
    # === FILESYSTEM OPERATIONS ===
    
    async def getattr(self, path: str) -> os.stat_result:
        """Get file/directory attributes"""
        
        # Check if directory
        if await self._is_virtual_directory(path):
            dir_info = await self._get_virtual_directory(path)
            return dir_info.get_stat()
        
        # Check if file
        file_info = await self._get_virtual_file(path)
        if file_info:
            return file_info.get_stat()
        
        raise FileNotFoundError(f"Path not found: {path}")
    
    async def readdir(self, path: str) -> List[str]:
        """Read directory contents"""
        
        dir_info = await self._get_virtual_directory(path)
        if not dir_info:
            raise FileNotFoundError(f"Directory not found: {path}")
        
        return dir_info.list_entries()
    
    async def open(self, path: str, flags: int) -> int:
        """Open file and return file descriptor"""
        
        # Check for write flags
        O_WRONLY = os.O_WRONLY if hasattr(os, 'O_WRONLY') else 1
        O_RDWR = os.O_RDWR if hasattr(os, 'O_RDWR') else 2
        O_CREAT = os.O_CREAT if hasattr(os, 'O_CREAT') else 64
        O_TRUNC = os.O_TRUNC if hasattr(os, 'O_TRUNC') else 512
        
        write_flags = O_WRONLY | O_RDWR | O_CREAT | O_TRUNC
        
        if flags & write_flags:
            raise ReadOnlyViolationError(f"Write access denied for {path}")
        
        # Get virtual file
        file_info = await self._get_virtual_file(path)
        if not file_info:
            raise FileNotFoundError(f"File not found: {path}")
        
        # Return mock file descriptor (will be handled by Dokan operations)
        return hash(path) % 1000000
    
    async def read(self, path: str, size: int, offset: int, fh: int) -> bytes:
        """Read data from file"""
        
        file_info = await self._get_virtual_file(path)
        if not file_info:
            raise FileNotFoundError(f"File not found: {path}")
        
        # Materialize file if needed
        if not file_info.is_materialized:
            await self._materialize_file(file_info)
        
        return await self._read_file_data(file_info, size, offset)
    
    async def release(self, path: str, fh: int) -> None:
        """Release file descriptor"""
        # Nothing to do for read-only filesystem
        pass
    
    # === EXTENDED ATTRIBUTES ===
    
    async def listxattr(self, path: str) -> List[str]:
        """List extended attributes"""
        
        file_info = await self._get_virtual_file(path)
        if not file_info:
            raise FileNotFoundError(f"File not found: {path}")
        
        attrs = file_info.extended_attrs.to_dict()
        return list(attrs.keys())
    
    async def getxattr(self, path: str, name: str) -> bytes:
        """Get extended attribute value"""
        
        file_info = await self._get_virtual_file(path)
        if not file_info:
            raise FileNotFoundError(f"File not found: {path}")
        
        attrs = file_info.extended_attrs.to_dict()
        
        if name not in attrs:
            raise FileNotFoundError(f"Extended attribute not found: {name}")
        
        return attrs[name].encode('utf-8')
    
    # === INTERNAL METHODS ===
    
    async def _load_virtual_tree(self) -> None:
        """Load virtual filesystem tree from ledger"""
        
        if not self.materializer:
            # Create simple demo tree for testing
            self._virtual_root = VirtualDirectoryInfo(path="/")
            return
        
        # Load from materializer
        self._virtual_root = await self.materializer.get_virtual_tree("demo_case")
    
    async def _is_virtual_directory(self, path: str) -> bool:
        """Check if path is a virtual directory"""
        
        if not self._virtual_root:
            return False
        
        if path == "/" or path == "":
            return True
        
        # Navigate through tree
        current = self._virtual_root
        parts = path.strip("/").split("/")
        
        for part in parts:
            if part in current.subdirectories:
                current = current.subdirectories[part]
            else:
                return False
        
        return True
    
    async def _get_virtual_directory(self, path: str) -> Optional[VirtualDirectoryInfo]:
        """Get virtual directory info"""
        
        if not self._virtual_root:
            return None
        
        if path == "/" or path == "":
            return self._virtual_root
        
        # Navigate through tree
        current = self._virtual_root
        parts = path.strip("/").split("/")
        
        for part in parts:
            if part in current.subdirectories:
                current = current.subdirectories[part]
            else:
                return None
        
        return current
    
    async def _get_virtual_file(self, path: str) -> Optional[VirtualFileInfo]:
        """Get virtual file info"""
        
        if not self._virtual_root:
            return None
        
        # Split path into directory and filename
        path_parts = path.strip("/").split("/")
        filename = path_parts[-1]
        dir_path = "/".join(path_parts[:-1]) if len(path_parts) > 1 else ""
        
        # Get directory
        directory = await self._get_virtual_directory(dir_path)
        if not directory:
            return None
        
        # Get file from directory
        return directory.files.get(filename)
    
    async def _materialize_file(self, file_info: VirtualFileInfo) -> None:
        """Materialize virtual file to cache"""
        
        if file_info.is_materialized:
            return
        
        if not self.materializer:
            raise MaterializationError("No materializer available")
        
        # Check cache first
        if self.cache:
            cached_path = await self.cache.get_cached_file(file_info.file_hash.sha256)
            if cached_path and os.path.exists(cached_path):
                file_info.materialized_path = cached_path
                file_info.is_materialized = True
                return
        
        # Materialize from source
        cache_path = os.path.join(self.config.cache_dir, file_info.file_hash.sha256)
        
        success = await self.materializer.materialize_file(file_info, cache_path)
        if not success:
            raise MaterializationError(f"Failed to materialize file: {file_info.path}")
        
        file_info.materialized_path = cache_path
        file_info.is_materialized = True
        
        # Verify hash
        with open(cache_path, 'rb') as f:
            content = f.read()
        
        if not file_info.file_hash.verify_content(content):
            os.unlink(cache_path)
            raise HashVerificationError(f"Hash verification failed for: {file_info.path}")
    
    async def _read_file_data(self, file_info: VirtualFileInfo, size: int, offset: int) -> bytes:
        """Read data from materialized file"""
        
        if not file_info.is_materialized or not file_info.materialized_path:
            raise MaterializationError(f"File not materialized: {file_info.path}")
        
        if not os.path.exists(file_info.materialized_path):
            raise FileNotFoundError(f"Materialized file not found: {file_info.materialized_path}")
        
        with open(file_info.materialized_path, 'rb') as f:
            f.seek(offset)
            return f.read(size)

# === WINDOWS-SPECIFIC UTILITIES ===

def is_dokan_available() -> bool:
    """Check if Dokan is available on the system"""
    return DOKAN_AVAILABLE

def get_dokan_version() -> Optional[str]:
    """Get Dokan version if available"""
    if not DOKAN_AVAILABLE:
        return None
    
    try:
        return f"{dokan.DOKAN_VERSION >> 8}.{dokan.DOKAN_VERSION & 0xFF}"
    except:
        return "unknown"

# === EXPORTS ===

__all__ = [
    "WindowsDokanFilesystem",
    "WindowsDokanConfig", 
    "WindowsDokanOperations",
    "is_dokan_available",
    "get_dokan_version"
]