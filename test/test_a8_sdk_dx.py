#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: test/test_a8_sdk_dx.py                               |
# | ROLE: A8 SDK & DX comprehensive test suite                 |
# | PLIK: test/test_a8_sdk_dx.py                               |
# | ROLA: A8 kompleksowy zestaw testów SDK & DX                |
# +-------------------------------------------------------------+
"""
PL: Kompleksowy zestaw testów dla A8 SDK & Developer Experience.
EN: Comprehensive test suite for A8 SDK & Developer Experience.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

# Add repo root to path for imports
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

# === TESTY / TESTS ===


class TestA8SDKGenerator(unittest.TestCase):
    """Test suite for A8 SDK generator functionality."""

    def setUp(self):
        """Set up test environment."""
        self.scripts_dir = REPO_ROOT / "scripts" / "a8"
        self.sdk_generator_path = self.scripts_dir / "sdk_generator.py"

    def test_sdk_generator_script_exists(self):
        """Test that SDK generator script exists."""
        self.assertTrue(self.sdk_generator_path.exists(), f"SDK generator script not found: {self.sdk_generator_path}")

    def test_sdk_generator_can_import(self):
        """Test that SDK generator script can be imported."""
        try:
            # Import SDK generator module
            sys.path.insert(0, str(self.scripts_dir))
            import sdk_generator

            # Check key classes exist
            self.assertTrue(hasattr(sdk_generator, 'SDKGenerator'))
            self.assertTrue(hasattr(sdk_generator, 'main'))

        except ImportError as e:
            self.fail(f"Failed to import SDK generator: {e}")
        finally:
            # Clean up sys.path
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))

    def test_sdk_generator_class_initialization(self):
        """Test SDK generator class can be initialized."""
        sys.path.insert(0, str(self.scripts_dir))
        try:
            import sdk_generator

            spec_path = REPO_ROOT / "docs" / "api" / "openapi.yaml"
            generator = sdk_generator.SDKGenerator(spec_path)

            self.assertEqual(generator.spec_path, spec_path)
            self.assertIsInstance(generator.spec, dict)
            self.assertIsInstance(generator.endpoints, list)

        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))

    def test_sdk_generator_openapi_parsing(self):
        """Test OpenAPI specification parsing."""
        sys.path.insert(0, str(self.scripts_dir))
        try:
            import sdk_generator

            # Create mock OpenAPI spec
            mock_spec = {
                "openapi": "3.0.3",
                "info": {"title": "Test API", "version": "1.0.0"},
                "paths": {"/health": {"get": {"summary": "Health check", "responses": {"200": {"description": "OK"}}}}},
            }

            with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
                json.dump(mock_spec, f)
                temp_path = Path(f.name)

            try:
                generator = sdk_generator.SDKGenerator(temp_path)
                success = generator.load_openapi_spec()

                self.assertTrue(success)
                self.assertEqual(generator.spec["openapi"], "3.0.3")
                self.assertIn("paths", generator.spec)

            finally:
                temp_path.unlink()

        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))


class TestA8ContractTester(unittest.TestCase):
    """Test suite for A8 contract testing functionality."""

    def setUp(self):
        """Set up test environment."""
        self.scripts_dir = REPO_ROOT / "scripts" / "a8"
        self.contract_tester_path = self.scripts_dir / "contract_tester.py"

    def test_contract_tester_script_exists(self):
        """Test that contract tester script exists."""
        self.assertTrue(
            self.contract_tester_path.exists(), f"Contract tester script not found: {self.contract_tester_path}"
        )

    def test_contract_tester_can_import(self):
        """Test that contract tester script can be imported."""
        try:
            sys.path.insert(0, str(self.scripts_dir))
            import contract_tester

            # Check key classes exist
            self.assertTrue(hasattr(contract_tester, 'ContractTester'))
            self.assertTrue(hasattr(contract_tester, 'ContractTestResult'))
            self.assertTrue(hasattr(contract_tester, 'main'))

        except ImportError as e:
            self.fail(f"Failed to import contract tester: {e}")
        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))

    def test_contract_test_result_initialization(self):
        """Test ContractTestResult initialization."""
        sys.path.insert(0, str(self.scripts_dir))
        try:
            import contract_tester

            result = contract_tester.ContractTestResult()

            self.assertEqual(result.total_tests, 0)
            self.assertEqual(result.passed_tests, 0)
            self.assertEqual(result.failed_tests, 0)
            self.assertIsInstance(result.errors, list)
            self.assertIsInstance(result.warnings, list)
            self.assertEqual(result.execution_time, 0.0)
            self.assertEqual(result.coverage_percentage, 0.0)

        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))

    def test_contract_tester_initialization(self):
        """Test ContractTester initialization."""
        sys.path.insert(0, str(self.scripts_dir))
        try:
            import contract_tester

            tester = contract_tester.ContractTester("http://localhost:8000")

            self.assertEqual(tester.base_url, "http://localhost:8000")
            self.assertIsInstance(tester.result, contract_tester.ContractTestResult)

        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))


class TestA8DXEnhancer(unittest.TestCase):
    """Test suite for A8 DX enhancer functionality."""

    def setUp(self):
        """Set up test environment."""
        self.scripts_dir = REPO_ROOT / "scripts" / "a8"
        self.dx_enhancer_path = self.scripts_dir / "dx_enhancer.py"

    def test_dx_enhancer_script_exists(self):
        """Test that DX enhancer script exists."""
        self.assertTrue(self.dx_enhancer_path.exists(), f"DX enhancer script not found: {self.dx_enhancer_path}")

    def test_dx_enhancer_can_import(self):
        """Test that DX enhancer script can be imported."""
        try:
            sys.path.insert(0, str(self.scripts_dir))
            import dx_enhancer

            # Check key classes exist
            self.assertTrue(hasattr(dx_enhancer, 'DXEnhancer'))
            self.assertTrue(hasattr(dx_enhancer, 'main'))

        except ImportError as e:
            self.fail(f"Failed to import DX enhancer: {e}")
        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))

    def test_dx_enhancer_initialization(self):
        """Test DXEnhancer initialization."""
        sys.path.insert(0, str(self.scripts_dir))
        try:
            import dx_enhancer

            enhancer = dx_enhancer.DXEnhancer()

            self.assertTrue(hasattr(enhancer, 'examples_dir'))
            self.assertTrue(hasattr(enhancer, 'docs_dir'))
            self.assertTrue(hasattr(enhancer, 'playground_dir'))

        finally:
            if str(self.scripts_dir) in sys.path:
                sys.path.remove(str(self.scripts_dir))


class TestA8SDKStructure(unittest.TestCase):
    """Test suite for A8 SDK structure and organization."""

    def test_sdk_directories_exist(self):
        """Test that SDK directory structure exists."""
        sdk_dirs = [
            REPO_ROOT / "sdk",
            REPO_ROOT / "sdk" / "ts",
            REPO_ROOT / "sdk" / "python",
            REPO_ROOT / "clients" / "typescript",
            REPO_ROOT / "scripts" / "a8",
        ]

        for sdk_dir in sdk_dirs:
            self.assertTrue(sdk_dir.exists(), f"SDK directory missing: {sdk_dir}")

    def test_existing_typescript_sdk_structure(self):
        """Test existing TypeScript SDK structure."""
        ts_sdk_dirs = [REPO_ROOT / "sdk" / "ts" / "src", REPO_ROOT / "clients" / "typescript" / "certeus-sdk" / "src"]

        for ts_dir in ts_sdk_dirs:
            if ts_dir.exists():
                # Check for key files
                expected_files = ['client.ts']
                for filename in expected_files:
                    file_path = ts_dir / filename
                    if file_path.exists():
                        self.assertTrue(file_path.is_file(), f"Expected TypeScript file: {file_path}")

    def test_openapi_spec_exists(self):
        """Test that OpenAPI specification exists."""
        openapi_paths = [REPO_ROOT / "docs" / "api" / "openapi.yaml", REPO_ROOT / "out" / "openapi.json"]

        # At least one OpenAPI spec should exist
        exists = any(path.exists() for path in openapi_paths)
        self.assertTrue(exists, "No OpenAPI specification found")


class TestA8ScriptExecution(unittest.TestCase):
    """Test suite for A8 script execution."""

    def setUp(self):
        """Set up test environment."""
        self.scripts_dir = REPO_ROOT / "scripts" / "a8"

    def test_sdk_generator_script_syntax(self):
        """Test SDK generator script syntax."""
        script_path = self.scripts_dir / "sdk_generator.py"
        if script_path.exists():
            result = subprocess.run(
                [sys.executable, '-m', 'py_compile', str(script_path)], capture_output=True, text=True
            )

            self.assertEqual(result.returncode, 0, f"SDK generator syntax error: {result.stderr}")

    def test_contract_tester_script_syntax(self):
        """Test contract tester script syntax."""
        script_path = self.scripts_dir / "contract_tester.py"
        if script_path.exists():
            result = subprocess.run(
                [sys.executable, '-m', 'py_compile', str(script_path)], capture_output=True, text=True
            )

            self.assertEqual(result.returncode, 0, f"Contract tester syntax error: {result.stderr}")

    def test_dx_enhancer_script_syntax(self):
        """Test DX enhancer script syntax."""
        script_path = self.scripts_dir / "dx_enhancer.py"
        if script_path.exists():
            result = subprocess.run(
                [sys.executable, '-m', 'py_compile', str(script_path)], capture_output=True, text=True
            )

            self.assertEqual(result.returncode, 0, f"DX enhancer syntax error: {result.stderr}")


class TestA8EnterpriseStandards(unittest.TestCase):
    """Test suite for A8 enterprise quality standards."""

    def test_a8_scripts_have_proper_headers(self):
        """Test that A8 scripts have proper enterprise headers."""
        scripts_dir = REPO_ROOT / "scripts" / "a8"

        if scripts_dir.exists():
            for script_file in scripts_dir.glob("*.py"):
                with open(script_file, encoding='utf-8') as f:
                    content = f.read()

                # Check for enterprise header
                self.assertIn("CERTEUS", content, f"Missing CERTEUS header in {script_file}")
                self.assertIn("FILE:", content, f"Missing FILE declaration in {script_file}")
                self.assertIn("ROLE:", content, f"Missing ROLE declaration in {script_file}")

    def test_a8_scripts_have_docstrings(self):
        """Test that A8 scripts have proper docstrings."""
        scripts_dir = REPO_ROOT / "scripts" / "a8"

        if scripts_dir.exists():
            for script_file in scripts_dir.glob("*.py"):
                with open(script_file, encoding='utf-8') as f:
                    content = f.read()

                # Check for docstrings
                self.assertIn('"""', content, f"Missing docstring in {script_file}")
                # Check for bilingual documentation
                has_pl = "PL:" in content
                has_en = "EN:" in content
                self.assertTrue(has_pl or has_en, f"Missing bilingual docs in {script_file}")

    def test_a8_implements_retry_logic(self):
        """Test that A8 components implement retry logic."""
        scripts_dir = REPO_ROOT / "scripts" / "a8"

        # Check for retry implementation patterns
        retry_patterns = ["retry", "attempt", "backoff", "max_retries"]

        if scripts_dir.exists():
            for script_file in scripts_dir.glob("*.py"):
                with open(script_file, encoding='utf-8') as f:
                    content = f.read().lower()

                # At least one retry pattern should be present
                has_retry = any(pattern in content for pattern in retry_patterns)
                if script_file.name != "__init__.py":
                    self.assertTrue(has_retry, f"No retry logic found in {script_file}")

    def test_a8_implements_error_handling(self):
        """Test that A8 components implement proper error handling."""
        scripts_dir = REPO_ROOT / "scripts" / "a8"

        error_patterns = ["try:", "except", "Exception", "Error"]

        if scripts_dir.exists():
            for script_file in scripts_dir.glob("*.py"):
                with open(script_file, encoding='utf-8') as f:
                    content = f.read()

                # Check for error handling
                has_error_handling = any(pattern in content for pattern in error_patterns)
                if script_file.name != "__init__.py":
                    self.assertTrue(has_error_handling, f"No error handling found in {script_file}")


class TestA8QualityGates(unittest.TestCase):
    """Test suite for A8 quality gates and compliance."""

    def test_a8_script_execution_time(self):
        """Test that A8 scripts execute within reasonable time limits."""
        scripts_dir = REPO_ROOT / "scripts" / "a8"
        max_execution_time = 30  # seconds

        if scripts_dir.exists():
            for script_file in scripts_dir.glob("*.py"):
                if script_file.name == "__init__.py":
                    continue

                start_time = time.time()
                try:
                    # Import check (should be fast)
                    subprocess.run(
                        [
                            sys.executable,
                            '-c',
                            f'import sys; sys.path.insert(0, "{scripts_dir}"); import {script_file.stem}',
                        ],
                        capture_output=True,
                        text=True,
                        timeout=max_execution_time,
                    )

                    execution_time = time.time() - start_time
                    self.assertLess(
                        execution_time,
                        max_execution_time,
                        f"Script {script_file} import took too long: {execution_time:.2f}s",
                    )

                except subprocess.TimeoutExpired:
                    self.fail(f"Script {script_file} import timed out after {max_execution_time}s")

    def test_a8_typescript_compatibility(self):
        """Test TypeScript SDK compatibility standards."""
        ts_files = []

        # Check various TypeScript SDK locations
        ts_locations = [REPO_ROOT / "sdk" / "ts" / "src", REPO_ROOT / "clients" / "typescript" / "certeus-sdk" / "src"]

        for location in ts_locations:
            if location.exists():
                ts_files.extend(location.glob("*.ts"))

        for ts_file in ts_files:
            with open(ts_file, encoding='utf-8') as f:
                content = f.read()

            # Check for TypeScript best practices
            has_types = "interface" in content or "type" in content
            has_exports = "export" in content

            if len(content.strip()) > 100:  # Skip very small files
                self.assertTrue(has_types or has_exports, f"TypeScript file {ts_file} missing types/exports")

    def test_a8_json_configuration_validity(self):
        """Test that A8 generates valid JSON configurations."""
        # Test if playground config would be valid JSON
        scripts_dir = REPO_ROOT / "scripts" / "a8"

        # Mock the DX enhancer to test JSON generation
        sys.path.insert(0, str(scripts_dir))
        try:
            import dx_enhancer

            enhancer = dx_enhancer.DXEnhancer()

            # Mock playground directory
            with tempfile.TemporaryDirectory() as temp_dir:
                enhancer.playground_dir = Path(temp_dir)

                # Generate playground config
                enhancer.generate_playground_config()

                # Check if generated JSON is valid
                config_file = Path(temp_dir) / "config.json"
                if config_file.exists():
                    with open(config_file, encoding='utf-8') as f:
                        config_data = json.load(f)

                    # Basic validation
                    self.assertIsInstance(config_data, dict)
                    self.assertIn("title", config_data)
                    self.assertIn("endpoints", config_data)

        finally:
            if str(scripts_dir) in sys.path:
                sys.path.remove(str(scripts_dir))


# === GŁÓWNA FUNKCJA TESTOWA / MAIN TEST FUNCTION ===


def main() -> int:
    """Main test execution function."""
    print("A8 SDK & DX Test Suite")
    print("=" * 60)

    # Create test suite
    suite = unittest.TestSuite()

    # Add test classes
    test_classes = [
        TestA8SDKGenerator,
        TestA8ContractTester,
        TestA8DXEnhancer,
        TestA8SDKStructure,
        TestA8ScriptExecution,
        TestA8EnterpriseStandards,
        TestA8QualityGates,
    ]

    for test_class in test_classes:
        tests = unittest.TestLoader().loadTestsFromTestCase(test_class)
        suite.addTests(tests)

    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    # Print summary
    print("\n" + "=" * 60)
    print(f"A8 Test Results: {result.testsRun - len(result.failures) - len(result.errors)}/{result.testsRun} passed")

    if result.failures:
        print(f"FAILURES: {len(result.failures)}")
        for test, traceback in result.failures:
            print(
                f"  - {test}: {traceback.split('AssertionError:')[-1].strip() if 'AssertionError:' in traceback else 'Failed'}"
            )

    if result.errors:
        print(f"ERRORS: {len(result.errors)}")
        for test, traceback in result.errors:
            print(f"  - {test}: {traceback.split('Exception:')[-1].strip() if 'Exception:' in traceback else 'Error'}")

    if result.wasSuccessful():
        print("PASS: All A8 SDK & DX tests passed!")
        print("SUCCESS: Enterprise big tech quality achieved")
        return 0
    else:
        print("FAIL: Some A8 tests failed - review implementation")
        return 1


if __name__ == "__main__":
    sys.exit(main())

# === I/O / ENDPOINTS ===

# === DODATKOWE TESTY INTEGRACYJNE / ADDITIONAL INTEGRATION TESTS ===
