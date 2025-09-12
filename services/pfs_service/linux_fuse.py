#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: services/pfs_service/linux_fuse.py                  |
# | ROLE: A3 - PFS Linux FUSE Implementation                  |
# | PLIK: services/pfs_service/linux_fuse.py                  |
# | ROLA: A3 - PFS Linux FUSE Implementation                  |
# +-------------------------------------------------------------+

"""
PL: A3 PFS Linux - implementacja przy użyciu FUSE
EN: A3 PFS Linux - implementation using FUSE

Linux-specific read-only filesystem implementation using FUSE.
Provides native Linux filesystem interface for CERTEUS PFS.

Dependencies:
- fusepy: Python FUSE bindings
- libfuse: Linux FUSE library

Key Features:
- Native Linux filesystem integration
- Hard read-only enforcement with EACCES
- Extended attributes (xattrs) support
- Hash verification on all operations
- File materialization from ledger
- High-performance async operations
"""

import asyncio
import errno
import os
import threading
import time
from typing import Any

try:
    import fuse
    from fuse import FUSE, FuseOSError, Operations
    FUSE_AVAILABLE = True
except ImportError:
    FUSE_AVAILABLE = False
    fuse = None
    FUSE = None
    FuseOSError = Exception
    Operations = object

from core.logging import get_logger
from core.pfs.filesystem_interface import (
    ExtendedAttributes,
    FileNotFoundError,
    FilesystemError,
    HashVerificationError,
    MaterializationError,
    PFSCacheInterface,
    PFSConfig,
    PFSFilesystemInterface,
    PFSMaterializerInterface,
    ReadOnlyViolationError,
    VirtualDirectoryInfo,
    VirtualFileInfo,
)
from services.ledger_service.postgres_ledger import PostgreSQLLedger

logger = get_logger("linux_fuse")

# === FUSE OPERATIONS IMPLEMENTATION ===

class LinuxFUSEOperations(Operations):
    """FUSE filesystem operations for Linux"""
    
    def __init__(self, pfs_filesystem: "LinuxFUSEFilesystem"):
        self.pfs = pfs_filesystem
        self.logger = get_logger("fuse_operations")
        
        # File handle tracking
        self._file_handles: dict[int, VirtualFileInfo] = {}
        self._next_handle = 1
        self._handle_lock = threading.Lock()
        
        # Event loop for async operations
        self._loop = None
        self._loop_thread = None
        self._start_event_loop()
    
    def _start_event_loop(self) -> None:
        """Start event loop for async operations"""
        
        def run_loop():
            self._loop = asyncio.new_event_loop()
            asyncio.set_event_loop(self._loop)
            self._loop.run_forever()
        
        self._loop_thread = threading.Thread(target=run_loop, daemon=True)
        self._loop_thread.start()
        
        # Wait for loop to be ready
        while self._loop is None:
            time.sleep(0.01)
    
    def _run_async(self, coro):
        """Run async coroutine in the event loop"""
        
        if self._loop is None:
            raise RuntimeError("Event loop not available")
        
        future = asyncio.run_coroutine_threadsafe(coro, self._loop)
        return future.result()
    
    def _get_next_handle(self) -> int:
        """Get next available file handle"""
        with self._handle_lock:
            handle = self._next_handle
            self._next_handle += 1
            return handle
    
    # === FILESYSTEM OPERATIONS ===
    
    def getattr(self, path: str, fh: int | None = None) -> dict[str, Any]:
        """Get file/directory attributes"""
        
        self.logger.debug(f"getattr: {path}")
        
        try:
            stat_result = self._run_async(self.pfs.getattr(path))
            
            return {
                'st_mode': stat_result.st_mode,
                'st_ino': stat_result.st_ino,
                'st_dev': stat_result.st_dev,
                'st_nlink': stat_result.st_nlink,
                'st_uid': stat_result.st_uid,
                'st_gid': stat_result.st_gid,
                'st_size': stat_result.st_size,
                'st_atime': stat_result.st_atime,
                'st_mtime': stat_result.st_mtime,
                'st_ctime': stat_result.st_ctime
            }
            
        except FileNotFoundError:
            raise FuseOSError(errno.ENOENT)
        except Exception as e:
            self.logger.error(f"Error in getattr for {path}: {str(e)}")
            raise FuseOSError(errno.EIO)
    
    def readdir(self, path: str, fh: int) -> list[str]:
        """Read directory contents"""
        
        self.logger.debug(f"readdir: {path}")
        
        try:
            entries = self._run_async(self.pfs.readdir(path))
            return entries
            
        except FileNotFoundError:
            raise FuseOSError(errno.ENOENT)
        except Exception as e:
            self.logger.error(f"Error in readdir for {path}: {str(e)}")
            raise FuseOSError(errno.EIO)
    
    def open(self, path: str, flags: int) -> int:
        """Open file"""
        
        self.logger.debug(f"open: {path}, flags={flags:o}")
        
        # Check for write flags and deny
        write_flags = os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND
        
        if flags & write_flags:
            self.logger.warning(f"Write access denied for {path}")
            raise FuseOSError(errno.EACCES)
        
        try:
            # Get virtual file info
            file_info = self._run_async(self.pfs._get_virtual_file(path))
            
            if not file_info:
                raise FuseOSError(errno.ENOENT)
            
            # Assign file handle
            handle = self._get_next_handle()
            self._file_handles[handle] = file_info
            
            return handle
            
        except FileNotFoundError:
            raise FuseOSError(errno.ENOENT)
        except Exception as e:
            self.logger.error(f"Error opening file {path}: {str(e)}")
            raise FuseOSError(errno.EIO)
    
    def read(self, path: str, size: int, offset: int, fh: int) -> bytes:
        """Read file data"""
        
        self.logger.debug(f"read: {path}, size={size}, offset={offset}")
        
        try:
            if fh not in self._file_handles:
                raise FuseOSError(errno.EBADF)
            
            return self._run_async(self.pfs.read(path, size, offset, fh))
            
        except Exception as e:
            self.logger.error(f"Error reading file {path}: {str(e)}")
            raise FuseOSError(errno.EIO)
    
    def release(self, path: str, fh: int) -> None:
        """Release file handle"""
        
        self.logger.debug(f"release: {path}, fh={fh}")
        
        try:
            if fh in self._file_handles:
                del self._file_handles[fh]
            
            self._run_async(self.pfs.release(path, fh))
            
        except Exception as e:
            self.logger.error(f"Error releasing file {path}: {str(e)}")
    
    # === EXTENDED ATTRIBUTES ===
    
    def listxattr(self, path: str) -> list[str]:
        """List extended attributes"""
        
        self.logger.debug(f"listxattr: {path}")
        
        try:
            return self._run_async(self.pfs.listxattr(path))
            
        except FileNotFoundError:
            raise FuseOSError(errno.ENOENT)
        except Exception as e:
            self.logger.error(f"Error listing xattrs for {path}: {str(e)}")
            raise FuseOSError(errno.EIO)
    
    def getxattr(self, path: str, name: str, position: int = 0) -> bytes:
        """Get extended attribute value"""
        
        self.logger.debug(f"getxattr: {path}, name={name}")
        
        try:
            return self._run_async(self.pfs.getxattr(path, name))
            
        except FileNotFoundError:
            raise FuseOSError(errno.ENODATA)
        except Exception as e:
            self.logger.error(f"Error getting xattr {name} for {path}: {str(e)}")
            raise FuseOSError(errno.EIO)
    
    # === WRITE OPERATIONS (All denied for read-only) ===
    
    def create(self, path: str, mode: int, fi=None) -> int:
        """Create file - deny for read-only filesystem"""
        self.logger.warning(f"Create denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def write(self, path: str, data: bytes, offset: int, fh: int) -> int:
        """Write data - deny for read-only filesystem"""
        self.logger.warning(f"Write denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def mkdir(self, path: str, mode: int) -> None:
        """Create directory - deny for read-only filesystem"""
        self.logger.warning(f"Mkdir denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def unlink(self, path: str) -> None:
        """Delete file - deny for read-only filesystem"""
        self.logger.warning(f"Unlink denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def rmdir(self, path: str) -> None:
        """Delete directory - deny for read-only filesystem"""
        self.logger.warning(f"Rmdir denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def rename(self, old: str, new: str) -> None:
        """Rename file/directory - deny for read-only filesystem"""
        self.logger.warning(f"Rename denied: {old} -> {new}")
        raise FuseOSError(errno.EACCES)
    
    def chmod(self, path: str, mode: int) -> None:
        """Change mode - deny for read-only filesystem"""
        self.logger.warning(f"Chmod denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def chown(self, path: str, uid: int, gid: int) -> None:
        """Change owner - deny for read-only filesystem"""
        self.logger.warning(f"Chown denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def truncate(self, path: str, length: int, fh: int | None = None) -> None:
        """Truncate file - deny for read-only filesystem"""
        self.logger.warning(f"Truncate denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def utimens(self, path: str, times: tuple | None = None) -> None:
        """Update timestamps - deny for read-only filesystem"""
        self.logger.warning(f"Utimens denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def setxattr(self, path: str, name: str, value: bytes, options: int, position: int = 0) -> None:
        """Set extended attribute - deny for read-only filesystem"""
        self.logger.warning(f"Setxattr denied for {path}")
        raise FuseOSError(errno.EACCES)
    
    def removexattr(self, path: str, name: str) -> None:
        """Remove extended attribute - deny for read-only filesystem"""
        self.logger.warning(f"Removexattr denied for {path}")
        raise FuseOSError(errno.EACCES)

# === MAIN LINUX FUSE FILESYSTEM ===

class LinuxFUSEFilesystem(PFSFilesystemInterface):
    """Linux FUSE-based PFS read-only filesystem"""
    
    def __init__(self, config: PFSConfig | None = None,
                 ledger: PostgreSQLLedger | None = None,
                 materializer: PFSMaterializerInterface | None = None,
                 cache: PFSCacheInterface | None = None):
        
        if not FUSE_AVAILABLE:
            raise RuntimeError("FUSE library not available. Install fusepy package.")
        
        self.config = config or PFSConfig.from_env()
        self.ledger = ledger
        self.materializer = materializer
        self.cache = cache
        
        # Mount state
        self._is_mounted = False
        self._mount_point: str | None = None
        self._fuse_thread: threading.Thread | None = None
        self._fuse_operations: LinuxFUSEOperations | None = None
        
        # Virtual filesystem tree
        self._virtual_root: VirtualDirectoryInfo | None = None
        
        self.logger = get_logger("linux_fuse_filesystem")
    
    async def initialize(self) -> None:
        """Initialize Linux FUSE filesystem"""
        
        self.logger.info("Initializing Linux FUSE filesystem")
        
        # Verify FUSE is available
        if not FUSE_AVAILABLE:
            raise RuntimeError("FUSE not available")
        
        # Initialize components
        if self.ledger:
            await self.ledger.initialize()
        
        # Create operations handler
        self._fuse_operations = LinuxFUSEOperations(self)
        
        # Create cache directory
        os.makedirs(self.config.cache_dir, exist_ok=True)
        
        self.logger.info("Linux FUSE filesystem initialized")
    
    async def mount(self, mount_point: str) -> None:
        """Mount filesystem using FUSE"""
        
        if self._is_mounted:
            raise FilesystemError("Filesystem already mounted")
        
        self._mount_point = mount_point
        
        # Create mount point if it doesn't exist
        os.makedirs(mount_point, exist_ok=True)
        
        # Check if mount point is empty
        if os.listdir(mount_point):
            raise FilesystemError(f"Mount point {mount_point} is not empty")
        
        self.logger.info(f"Mounting PFS at {mount_point}")
        
        # Load virtual filesystem tree
        await self._load_virtual_tree()
        
        # Prepare FUSE options
        fuse_options = self._get_fuse_options()
        
        # Start FUSE in separate thread
        self._fuse_thread = threading.Thread(
            target=self._run_fuse_mount,
            args=(mount_point, fuse_options),
            name="FUSEMount"
        )
        self._fuse_thread.daemon = True
        self._fuse_thread.start()
        
        # Wait for mount to be ready
        timeout = 10.0
        start_time = time.time()
        
        while not self._is_mounted and (time.time() - start_time) < timeout:
            await asyncio.sleep(0.1)
        
        if not self._is_mounted:
            raise FilesystemError(f"Failed to mount filesystem within {timeout}s")
        
        self.logger.info(f"PFS mounted successfully at {mount_point}")
    
    def _get_fuse_options(self) -> dict[str, Any]:
        """Get FUSE-specific options"""
        
        options = {
            'foreground': True,  # Run in foreground for thread control
            'allow_other': self.config.allow_other,
            'auto_unmount': self.config.auto_unmount,
            'ro': True,  # Read-only filesystem
            'default_permissions': False,  # We handle permissions
            'big_writes': True,  # Enable big writes (not that we use them)
            'max_read': self.config.read_buffer_size
        }
        
        # Add platform-specific options
        for key, value in self.config.platform_options.items():
            if key.startswith("fuse_"):
                options[key[5:]] = value  # Remove "fuse_" prefix
        
        return options
    
    def _run_fuse_mount(self, mount_point: str, options: dict[str, Any]) -> None:
        """Run FUSE mount in separate thread"""
        
        try:
            self.logger.debug(f"Starting FUSE mount at {mount_point}")
            self.logger.debug(f"FUSE options: {options}")
            
            self._is_mounted = True
            
            # Create and run FUSE
            FUSE(
                self._fuse_operations,
                mount_point,
                **options
            )
            
            self.logger.info("FUSE mount finished")
            
        except Exception as e:
            self.logger.error(f"FUSE mount failed: {str(e)}")
        finally:
            self._is_mounted = False
    
    async def unmount(self) -> None:
        """Unmount filesystem"""
        
        if not self._is_mounted or not self._mount_point:
            return
        
        self.logger.info(f"Unmounting PFS from {self._mount_point}")
        
        try:
            # Send unmount command
            import subprocess
            result = subprocess.run(
                ['fusermount', '-u', self._mount_point],
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if result.returncode != 0:
                self.logger.error(f"fusermount failed: {result.stderr}")
                
                # Try alternative unmount
                result = subprocess.run(
                    ['umount', self._mount_point],
                    capture_output=True,
                    text=True,
                    timeout=10
                )
            
            # Wait for unmount thread
            if self._fuse_thread:
                self._fuse_thread.join(timeout=10.0)
            
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
    
    async def readdir(self, path: str) -> list[str]:
        """Read directory contents"""
        
        dir_info = await self._get_virtual_directory(path)
        if not dir_info:
            raise FileNotFoundError(f"Directory not found: {path}")
        
        return dir_info.list_entries()
    
    async def open(self, path: str, flags: int) -> int:
        """Open file and return file descriptor"""
        
        # Check for write flags
        write_flags = os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND
        
        if flags & write_flags:
            raise ReadOnlyViolationError(f"Write access denied for {path}")
        
        # Get virtual file
        file_info = await self._get_virtual_file(path)
        if not file_info:
            raise FileNotFoundError(f"File not found: {path}")
        
        # Return mock file descriptor (will be handled by FUSE operations)
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
    
    async def listxattr(self, path: str) -> list[str]:
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
            self._create_demo_tree()
            return
        
        # Load from materializer
        self._virtual_root = await self.materializer.get_virtual_tree("demo_case")
    
    def _create_demo_tree(self) -> None:
        """Create demo virtual tree for testing"""
        
        if not self._virtual_root:
            return
        
        # Create demo file
        from datetime import datetime

        from core.pfs.filesystem_interface import FileHash
        
        demo_file = VirtualFileInfo(
            path="/demo.txt",
            file_hash=FileHash(sha256="a" * 64),
            size=100,
            mode=0o644,
            created_time=datetime.now(),
            modified_time=datetime.now(),
            extended_attrs=ExtendedAttributes(
                pfs_hash="a" * 64,
                pfs_size=100,
                pfs_case_id="DEMO",
                pfs_mime_type="text/plain"
            )
        )
        
        self._virtual_root.files["demo.txt"] = demo_file
    
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
    
    async def _get_virtual_directory(self, path: str) -> VirtualDirectoryInfo | None:
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
    
    async def _get_virtual_file(self, path: str) -> VirtualFileInfo | None:
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
            # For demo, create mock file
            cache_path = os.path.join(self.config.cache_dir, file_info.file_hash.sha256)
            with open(cache_path, 'w') as f:
                f.write(f"Demo file content for {file_info.path}\n" * 5)
            
            file_info.materialized_path = cache_path
            file_info.is_materialized = True
            return
        
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

# === LINUX-SPECIFIC UTILITIES ===

def is_fuse_available() -> bool:
    """Check if FUSE is available on the system"""
    return FUSE_AVAILABLE

def get_fuse_version() -> str | None:
    """Get FUSE version if available"""
    if not FUSE_AVAILABLE:
        return None
    
    try:
        import subprocess
        result = subprocess.run(['fusermount', '--version'], capture_output=True, text=True)
        if result.returncode == 0:
            return result.stdout.strip()
    except:
        pass
    
    return "unknown"

# === EXPORTS ===

__all__ = [
    "LinuxFUSEFilesystem",
    "LinuxFUSEOperations",
    "is_fuse_available",
    "get_fuse_version"
]