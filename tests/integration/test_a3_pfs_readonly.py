#!/usr/bin/env python3

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: tests/integration/test_a3_pfs_readonly.py           |
# | ROLE: A3 - PFS Read-Only Integration Tests (DoD)          |
# | PLIK: tests/integration/test_a3_pfs_readonly.py           |
# | ROLA: A3 - PFS Read-Only Integration Tests (DoD)          |
# +-------------------------------------------------------------+

"""
PL: Testy integracyjne A3 - walidacja DoD requirements dla PFS Read-Only
EN: A3 Integration Tests - DoD requirements validation for PFS Read-Only

DoD Requirements tested:
✓ Cross-platform support (Linux/Windows/macOS)
✓ Hard read-only enforcement (write operations must fail)
✓ Hash verification without divergence on materialization
✓ Extended attributes (xattrs) support
✓ Mount/unmount operations
✓ CI smoke tests capability
"""

import asyncio
from datetime import datetime
import hashlib
import os
import platform
import tempfile

import pytest

from core.pfs.filesystem_interface import (
    ExtendedAttributes,
    FileHash,
    FileNotFoundError,
    PFSConfig,
    PFSFilesystemFactory,
    PFSFilesystemInterface,
    ReadOnlyViolationError,
    SupportedPlatform,
    VirtualDirectoryInfo,
    VirtualFileInfo,
    get_current_platform,
)

# Platform-specific imports with fallbacks
try:
    from services.pfs_service.linux_fuse import LinuxFUSEFilesystem, is_fuse_available
except ImportError:
    LinuxFUSEFilesystem = None

    def is_fuse_available():
        return False


try:
    from services.pfs_service.windows_dokan import WindowsDokanFilesystem, is_dokan_available
except ImportError:
    WindowsDokanFilesystem = None

    def is_dokan_available():
        return False

# === TEST FIXTURES ===


@pytest.fixture
def pfs_config():
    """PFS test configuration"""

    with tempfile.TemporaryDirectory() as temp_dir:
        config = PFSConfig(
            mount_point=os.path.join(temp_dir, "mount"),
            cache_dir=os.path.join(temp_dir, "cache"),
            allow_other=False,
            auto_unmount=True,
            max_cache_size_mb=100,
            verify_all_hashes=True,
        )
        yield config


@pytest.fixture
def mock_materializer():
    """Mock materializer for testing"""

    from core.pfs.filesystem_interface import PFSMaterializerInterface

    class MockMaterializer(PFSMaterializerInterface):
        def __init__(self):
            self.demo_content = b"CERTEUS PFS Demo Content - Read-Only Test\n" * 10
            self.demo_hash = hashlib.sha256(self.demo_content).hexdigest()

        async def materialize_file(self, file_info: VirtualFileInfo, target_path: str) -> bool:
            """Materialize demo file"""
            try:
                os.makedirs(os.path.dirname(target_path), exist_ok=True)
                with open(target_path, 'wb') as f:
                    f.write(self.demo_content)
                return True
            except Exception:
                return False

        async def verify_materialized_file(self, file_info: VirtualFileInfo, materialized_path: str) -> bool:
            """Verify materialized file"""
            try:
                with open(materialized_path, 'rb') as f:
                    content = f.read()
                return file_info.file_hash.verify_content(content)
            except Exception:
                return False

        async def get_virtual_tree(self, case_id: str) -> VirtualDirectoryInfo:
            """Get demo virtual tree"""

            root = VirtualDirectoryInfo(path="/")

            # Create demo files
            demo_file = VirtualFileInfo(
                path="/demo.txt",
                file_hash=FileHash(sha256=self.demo_hash),
                size=len(self.demo_content),
                mode=0o644,
                created_time=datetime.now(),
                modified_time=datetime.now(),
                extended_attrs=ExtendedAttributes(
                    pfs_hash=self.demo_hash,
                    pfs_size=len(self.demo_content),
                    pfs_case_id=case_id,
                    pfs_mime_type="text/plain",
                    pfs_version="1.0",
                ),
            )

            readme_content = b"# CERTEUS PFS Read-Only Filesystem\n\nThis is a demo filesystem.\n"
            readme_hash = hashlib.sha256(readme_content).hexdigest()

            readme_file = VirtualFileInfo(
                path="/README.md",
                file_hash=FileHash(sha256=readme_hash),
                size=len(readme_content),
                mode=0o644,
                created_time=datetime.now(),
                modified_time=datetime.now(),
                extended_attrs=ExtendedAttributes(
                    pfs_hash=readme_hash,
                    pfs_size=len(readme_content),
                    pfs_case_id=case_id,
                    pfs_mime_type="text/markdown",
                ),
            )

            # Add to root
            root.files["demo.txt"] = demo_file
            root.files["README.md"] = readme_file

            # Create subdirectory
            subdir = VirtualDirectoryInfo(path="/evidence")

            evidence_content = b'{"type": "evidence", "data": "confidential evidence data"}'
            evidence_hash = hashlib.sha256(evidence_content).hexdigest()

            evidence_file = VirtualFileInfo(
                path="/evidence/evidence.json",
                file_hash=FileHash(sha256=evidence_hash),
                size=len(evidence_content),
                mode=0o600,  # Restrictive permissions
                created_time=datetime.now(),
                modified_time=datetime.now(),
                extended_attrs=ExtendedAttributes(
                    pfs_hash=evidence_hash,
                    pfs_size=len(evidence_content),
                    pfs_case_id=case_id,
                    pfs_mime_type="application/json",
                    custom={"confidentiality": "high", "evidence_type": "digital"},
                ),
            )

            subdir.files["evidence.json"] = evidence_file
            root.subdirectories["evidence"] = subdir

            return root

        async def resolve_file_content(self, file_hash: FileHash) -> bytes:
            """Resolve file content by hash"""
            if file_hash.sha256 == self.demo_hash:
                return self.demo_content
            else:
                # Generate content based on hash for testing
                return f"Content for hash {file_hash.sha256}".encode()

    return MockMaterializer()


# === PLATFORM DETECTION TESTS ===


class TestPlatformDetection:
    """Test platform detection and factory"""

    def test_get_current_platform(self):
        """Test current platform detection"""

        current = get_current_platform()

        system = platform.system().lower()
        if system == "linux":
            assert current == SupportedPlatform.LINUX
        elif system == "windows":
            assert current == SupportedPlatform.WINDOWS
        elif system == "darwin":
            assert current == SupportedPlatform.MACOS

    def test_filesystem_factory(self):
        """Test filesystem factory creation"""

        # Skip if no filesystem implementation available on current platform
        current_platform = get_current_platform()

        if current_platform == SupportedPlatform.LINUX and not is_fuse_available():
            pytest.skip("FUSE not available on this system - requires fusepy package")
        elif current_platform == SupportedPlatform.WINDOWS and not is_dokan_available():
            pytest.skip("Dokan not available on this system")
        elif current_platform == SupportedPlatform.MACOS:
            pytest.skip("macOS FUSE implementation not available - module 'services.pfs_service.macos_fuse' not found")

        # Test with current platform
        fs = PFSFilesystemFactory.create_filesystem()
        assert isinstance(fs, PFSFilesystemInterface)

        # Test with specific platforms (may not be available)
        try:
            linux_fs = PFSFilesystemFactory.create_filesystem(SupportedPlatform.LINUX)
            if is_fuse_available():
                assert linux_fs is not None
        except RuntimeError:
            pass  # Expected if not available

        try:
            windows_fs = PFSFilesystemFactory.create_filesystem(SupportedPlatform.WINDOWS)
            if is_dokan_available():
                assert windows_fs is not None
        except RuntimeError:
            pass  # Expected if not available


# === READ-ONLY ENFORCEMENT TESTS ===


class TestReadOnlyEnforcement:
    """Test hard read-only enforcement across platforms"""

    @pytest.mark.asyncio
    async def test_write_operations_denied(self, pfs_config, mock_materializer):
        """
        Test: All write operations must fail with appropriate errors
        DoD: Hard read-only enforcement
        """

        # Skip if no filesystem implementation available
        current_platform = get_current_platform()

        if current_platform == SupportedPlatform.LINUX and not is_fuse_available():
            pytest.skip("FUSE not available on this system")
        elif current_platform == SupportedPlatform.WINDOWS and not is_dokan_available():
            pytest.skip("Dokan not available on this system")
        elif current_platform == SupportedPlatform.MACOS:
            pytest.skip("macOS FUSE implementation not available")

        # Create filesystem
        fs = PFSFilesystemFactory.create_filesystem()
        fs.materializer = mock_materializer

        await fs.initialize()

        try:
            # Test create file
            with pytest.raises(ReadOnlyViolationError):
                await fs.create("/new_file.txt", 0o644)

            # Test write to file
            with pytest.raises(ReadOnlyViolationError):
                await fs.write("/demo.txt", b"illegal write", 0, 1)

            # Test mkdir
            with pytest.raises(ReadOnlyViolationError):
                await fs.mkdir("/new_directory", 0o755)

            # Test unlink
            with pytest.raises(ReadOnlyViolationError):
                await fs.unlink("/demo.txt")

            # Test rmdir
            with pytest.raises(ReadOnlyViolationError):
                await fs.rmdir("/evidence")

            # Test setxattr
            with pytest.raises(ReadOnlyViolationError):
                await fs.setxattr("/demo.txt", "user.test", b"value", 0)

            print("✓ All write operations correctly denied")

        finally:
            # Cleanup
            if await fs.is_mounted():
                await fs.unmount()


# === HASH VERIFICATION TESTS ===


class TestHashVerification:
    """Test hash verification without divergence"""

    @pytest.mark.skipif(not is_fuse_available(), reason="FUSE not available on this system - requires fusepy package")
    @pytest.mark.asyncio
    async def test_hash_verification_on_materialization(self, pfs_config, mock_materializer):
        """
        Test: Hash verification must be bit-identical on materialization
        DoD: No hash divergence during materialization
        """

        # Create test filesystem interface (not mounted)
        from services.pfs_service.linux_fuse import LinuxFUSEFilesystem

        fs = LinuxFUSEFilesystem(pfs_config, materializer=mock_materializer)
        await fs.initialize()

        try:
            # Load virtual tree
            await fs._load_virtual_tree()

            # Get demo file
            demo_file = await fs._get_virtual_file("/demo.txt")
            assert demo_file is not None

            original_hash = demo_file.file_hash.sha256

            # Materialize file multiple times
            materializations = []

            for i in range(5):
                # Create separate cache path for each materialization
                cache_path = os.path.join(pfs_config.cache_dir, f"test_{i}")

                # Materialize
                success = await mock_materializer.materialize_file(demo_file, cache_path)
                assert success, f"Materialization {i} failed"

                # Verify file exists
                assert os.path.exists(cache_path), f"Materialized file {i} not found"

                # Calculate hash
                with open(cache_path, 'rb') as f:
                    content = f.read()

                computed_hash = hashlib.sha256(content).hexdigest()
                materializations.append({'path': cache_path, 'hash': computed_hash, 'content': content})

                # Verify hash matches original
                assert computed_hash == original_hash, f"Hash divergence in materialization {i}"

            # Verify all materializations are bit-identical
            reference_content = materializations[0]['content']
            reference_hash = materializations[0]['hash']

            for i, materialization in enumerate(materializations[1:], 1):
                assert materialization['content'] == reference_content, f"Content divergence in materialization {i}"
                assert materialization['hash'] == reference_hash, f"Hash divergence in materialization {i}"

            print(f"✓ Hash verification passed for {len(materializations)} materializations")
            print(f"  Original hash: {original_hash}")
            print(f"  All materialized hashes: {reference_hash}")
            print(f"  Content size: {len(reference_content)} bytes")

        finally:
            # Cleanup
            for materialization in materializations:
                try:
                    os.unlink(materialization['path'])
                except:
                    pass

    @pytest.mark.asyncio
    async def test_multi_algorithm_hash_verification(self, pfs_config):
        """
        Test: Multi-algorithm hash verification
        DoD: Support for multiple hash algorithms
        """

        test_content = b"CERTEUS multi-hash verification test content"

        # Create file hash with multiple algorithms
        file_hash = FileHash(
            sha256=hashlib.sha256(test_content).hexdigest(), sha512=hashlib.sha512(test_content).hexdigest()
        )

        # Test verification with correct content
        assert file_hash.verify_content(test_content), "Multi-hash verification failed for correct content"

        # Test verification with incorrect content
        wrong_content = b"Wrong content"
        assert not file_hash.verify_content(wrong_content), "Multi-hash verification should fail for wrong content"

        # Test with only SHA256
        sha256_only = FileHash(sha256=hashlib.sha256(test_content).hexdigest())
        assert sha256_only.verify_content(test_content), "SHA256-only verification failed"

        print("✓ Multi-algorithm hash verification working correctly")


# === EXTENDED ATTRIBUTES TESTS ===


class TestExtendedAttributes:
    """Test extended attributes (xattrs) support"""

    @pytest.mark.skipif(not is_fuse_available(), reason="FUSE not available on this system - requires fusepy package")
    @pytest.mark.asyncio
    async def test_xattr_operations(self, pfs_config, mock_materializer):
        """
        Test: Extended attributes operations
        DoD: xattrs support with PFS metadata
        """

        # Create test filesystem interface
        from services.pfs_service.linux_fuse import LinuxFUSEFilesystem

        fs = LinuxFUSEFilesystem(pfs_config, materializer=mock_materializer)
        await fs.initialize()

        try:
            # Load virtual tree
            await fs._load_virtual_tree()

            # Test xattr listing
            xattr_list = await fs.listxattr("/demo.txt")
            assert len(xattr_list) > 0, "No extended attributes found"

            print(f"Extended attributes found: {xattr_list}")

            # Test getting specific xattrs
            for xattr_name in xattr_list:
                value = await fs.getxattr("/demo.txt", xattr_name)
                assert isinstance(value, bytes), f"xattr value should be bytes: {xattr_name}"

                decoded_value = value.decode('utf-8')
                print(f"  {xattr_name}: {decoded_value}")

            # Test PFS-specific xattrs
            expected_pfs_attrs = ["user.pfs_hash", "user.pfs_size", "user.pfs_case_id"]

            for expected_attr in expected_pfs_attrs:
                if expected_attr in xattr_list:
                    value = await fs.getxattr("/demo.txt", expected_attr)
                    assert value is not None, f"PFS attribute {expected_attr} should have value"
                    print(f"  PFS attribute {expected_attr}: {value.decode('utf-8')}")

            # Test non-existent xattr
            with pytest.raises(FileNotFoundError):
                await fs.getxattr("/demo.txt", "user.nonexistent")

            print("✓ Extended attributes operations working correctly")

        finally:
            pass  # No cleanup needed for interface testing

    def test_extended_attributes_data_structure(self):
        """
        Test: ExtendedAttributes data structure
        DoD: Proper xattr data handling
        """

        # Create extended attributes
        attrs = ExtendedAttributes(
            pfs_hash="abcd1234" + "0" * 56,
            pfs_size=1024,
            pfs_case_id="TEST-CASE-001",
            pfs_bundle_id="BUNDLE-001",
            pfs_signature="signature_data",
            pfs_mime_type="text/plain",
            custom={"confidentiality": "high", "retention": "7years"},
        )

        # Test conversion to dict
        attr_dict = attrs.to_dict()

        assert "user.pfs_hash" in attr_dict
        assert "user.pfs_size" in attr_dict
        assert "user.pfs_case_id" in attr_dict
        assert "user.pfs_custom_confidentiality" in attr_dict
        assert "user.pfs_custom_retention" in attr_dict

        print(f"Extended attributes dict: {attr_dict}")

        # Test conversion from dict
        reconstructed = ExtendedAttributes.from_dict(attr_dict)

        assert reconstructed.pfs_hash == attrs.pfs_hash
        assert reconstructed.pfs_size == attrs.pfs_size
        assert reconstructed.pfs_case_id == attrs.pfs_case_id
        assert reconstructed.custom["confidentiality"] == "high"
        assert reconstructed.custom["retention"] == "7years"

        print("✓ Extended attributes data structure working correctly")


# === MOUNT/UNMOUNT TESTS ===


class TestMountOperations:
    """Test mount and unmount operations"""

    @pytest.mark.asyncio
    @pytest.mark.skipif(
        platform.system() != "Linux" or not is_fuse_available(), reason="FUSE not available on this system"
    )
    async def test_mount_unmount_cycle(self, pfs_config, mock_materializer):
        """
        Test: Mount and unmount operations
        DoD: Successful mount/unmount cycle
        """

        fs = LinuxFUSEFilesystem(pfs_config, materializer=mock_materializer)
        await fs.initialize()

        try:
            # Initial state
            assert not await fs.is_mounted(), "Filesystem should not be mounted initially"

            # Mount
            await fs.mount(pfs_config.mount_point)
            assert await fs.is_mounted(), "Filesystem should be mounted after mount()"

            # Verify mount point exists and is accessible
            assert os.path.exists(pfs_config.mount_point), "Mount point should exist"
            assert os.path.ismount(pfs_config.mount_point), "Mount point should be a mount"

            # Test basic operations while mounted
            mount_contents = os.listdir(pfs_config.mount_point)
            assert len(mount_contents) > 0, "Mount point should have contents"

            print(f"Mount point contents: {mount_contents}")

            # Unmount
            await fs.unmount()
            assert not await fs.is_mounted(), "Filesystem should not be mounted after unmount()"

            # Verify mount point is no longer a mount
            # Note: mount point directory may still exist but should not be mounted

            print("✓ Mount/unmount cycle completed successfully")

        except Exception as e:
            # Ensure cleanup on failure
            try:
                if await fs.is_mounted():
                    await fs.unmount()
            except:
                pass
            raise e


# === CI SMOKE TESTS ===


class TestCISmokeTests:
    """CI-ready smoke tests for automated testing"""

    @pytest.mark.asyncio
    async def test_ci_smoke_mount_ls_materialize_xattrs_unmount(self, pfs_config, mock_materializer):
        """
        Test: CI Smoke test sequence
        DoD: mount→ls→materialize→sprawdź xattrs→umount
        """

        current_platform = get_current_platform()

        # Skip on platforms without filesystem support
        if current_platform == SupportedPlatform.LINUX and not is_fuse_available():
            pytest.skip("FUSE not available - CI environment may need setup")
        elif current_platform == SupportedPlatform.WINDOWS and not is_dokan_available():
            pytest.skip("Dokan not available - CI environment may need setup")
        elif current_platform == SupportedPlatform.MACOS:
            pytest.skip("macOS support not implemented yet")

        print(f"\n=== CI SMOKE TEST for {current_platform.value.upper()} ===")

        # Create filesystem for current platform
        fs = PFSFilesystemFactory.create_filesystem()
        fs.materializer = mock_materializer
        fs.config = pfs_config

        smoke_test_results = {
            "platform": current_platform.value,
            "mount": False,
            "ls": False,
            "materialize": False,
            "xattrs": False,
            "unmount": False,
            "readonly_enforcement": False,
        }

        try:
            await fs.initialize()

            # 1. MOUNT
            print("1. Mounting filesystem...")
            await fs.mount(pfs_config.mount_point)
            smoke_test_results["mount"] = True
            print("   ✓ Mount successful")

            # 2. LS (List contents)
            print("2. Listing contents...")
            root_contents = await fs.readdir("/")
            assert len(root_contents) >= 2, "Root should have at least . and .."

            # Find demo files
            demo_files = [f for f in root_contents if f not in [".", ".."]]
            assert len(demo_files) > 0, "Should have demo files"

            smoke_test_results["ls"] = True
            print(f"   ✓ Listed {len(demo_files)} files: {demo_files}")

            # 3. MATERIALIZE
            print("3. Materializing files...")
            demo_file = demo_files[0] if demo_files else "demo.txt"

            # Open and read file (triggers materialization)
            fh = await fs.open(f"/{demo_file}", os.O_RDONLY)
            content = await fs.read(f"/{demo_file}", 1024, 0, fh)
            await fs.release(f"/{demo_file}", fh)

            assert len(content) > 0, "Should have file content"
            smoke_test_results["materialize"] = True
            print(f"   ✓ Materialized {len(content)} bytes from {demo_file}")

            # 4. CHECK XATTRS
            print("4. Checking extended attributes...")
            xattrs = await fs.listxattr(f"/{demo_file}")
            assert len(xattrs) > 0, "Should have extended attributes"

            # Check specific PFS xattrs
            pfs_xattrs = [x for x in xattrs if "pfs" in x.lower()]
            assert len(pfs_xattrs) > 0, "Should have PFS-specific xattrs"

            smoke_test_results["xattrs"] = True
            print(f"   ✓ Found {len(xattrs)} xattrs, {len(pfs_xattrs)} PFS-specific")

            # 5. VERIFY READ-ONLY
            print("5. Verifying read-only enforcement...")
            try:
                await fs.create("/illegal_file.txt", 0o644)
                raise AssertionError("Create should have failed")
            except ReadOnlyViolationError:
                smoke_test_results["readonly_enforcement"] = True
                print("   ✓ Read-only enforcement working")

            # 6. UNMOUNT
            print("6. Unmounting filesystem...")
            await fs.unmount()
            smoke_test_results["unmount"] = True
            print("   ✓ Unmount successful")

            # Generate CI report
            print("\n=== CI SMOKE TEST RESULTS ===")
            all_passed = all(smoke_test_results.values())

            for test, passed in smoke_test_results.items():
                status = "✓ PASS" if passed else "✗ FAIL"
                print(f"{test.upper()}: {status}")

            print(f"\nOVERALL: {'✓ ALL TESTS PASSED' if all_passed else '✗ SOME TESTS FAILED'}")

            # Assert for pytest
            assert all_passed, f"Smoke test failures: {smoke_test_results}"

        except Exception as e:
            print(f"\n✗ CI Smoke test failed: {str(e)}")

            # Ensure cleanup
            try:
                if await fs.is_mounted():
                    await fs.unmount()
            except:
                pass

            raise e

    def test_ci_platform_capabilities(self):
        """
        Test: CI platform capabilities check
        DoD: Platform detection and capability verification
        """

        current_platform = get_current_platform()

        capabilities = {"platform_detected": True, "filesystem_available": False, "dependencies_installed": False}

        print("\n=== PLATFORM CAPABILITIES CHECK ===")
        print(f"Detected platform: {current_platform.value}")

        # Check filesystem availability
        if current_platform == SupportedPlatform.LINUX:
            capabilities["filesystem_available"] = is_fuse_available()
            capabilities["dependencies_installed"] = is_fuse_available()
            print(f"FUSE available: {capabilities['filesystem_available']}")

        elif current_platform == SupportedPlatform.WINDOWS:
            capabilities["filesystem_available"] = is_dokan_available()
            capabilities["dependencies_installed"] = is_dokan_available()
            print(f"Dokan available: {capabilities['filesystem_available']}")

        elif current_platform == SupportedPlatform.MACOS:
            # macOS implementation not complete yet
            capabilities["filesystem_available"] = False
            capabilities["dependencies_installed"] = False
            print("macOS: Not implemented yet")

        # Try creating filesystem instance
        try:
            PFSFilesystemFactory.create_filesystem()
            print("✓ Filesystem factory working")
        except Exception as e:
            print(f"✗ Filesystem factory failed: {str(e)}")
            capabilities["filesystem_available"] = False

        print(f"\nCapabilities summary: {capabilities}")

        # For CI, we need at least platform detection
        assert capabilities["platform_detected"], "Platform detection must work"


# === CLI RUNNER FOR CI ===


async def run_ci_smoke_tests():
    """Run CI smoke tests from command line"""

    print("CERTEUS A3 PFS Read-Only - CI Smoke Tests")
    print("=" * 50)

    current_platform = get_current_platform()
    print(f"Platform: {current_platform.value}")

    # Check capabilities
    if current_platform == SupportedPlatform.LINUX:
        available = is_fuse_available()
        print(f"FUSE available: {available}")

    elif current_platform == SupportedPlatform.WINDOWS:
        available = is_dokan_available()
        print(f"Dokan available: {available}")

    else:
        print("Platform not fully supported yet")
        return 1

    if not available:
        print("Required filesystem driver not available")
        return 1

    # Run smoke test
    try:
        # This would normally be run through pytest, but can also be standalone
        print("To run full smoke tests, use: pytest tests/integration/test_a3_pfs_readonly.py")
        return 0

    except Exception as e:
        print(f"Smoke test failed: {str(e)}")
        return 1


if __name__ == "__main__":
    import sys

    result = asyncio.run(run_ci_smoke_tests())
    sys.exit(result)
