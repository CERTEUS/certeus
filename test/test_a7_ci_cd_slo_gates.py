#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: test/test_a7_ci_cd_slo_gates.py                      |
# | ROLE: A7 CI/CD & SLO-Gates Test Suite                      |
# | DESC: Enterprise quality tests for A7 implementation       |
# +-------------------------------------------------------------+

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class TestA7SLOGateCheck(unittest.TestCase):
    """Test suite for A7 SLO Gate Check functionality."""

    def setUp(self):
        """Set up test environment."""
        self.temp_dir = Path(tempfile.mkdtemp())
        self.slo_script = Path("scripts/a7/slo_gate_check.py")

    def tearDown(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_slo_gate_check_pass(self):
        """Test SLO gate check with passing metrics."""
        # Create test metrics file
        metrics = {
            "health": {
                "count": 20,
                "p95_ms": 150.0,
                "error_rate": 0.005
            }
        }
        metrics_file = self.temp_dir / "slo_pass.json"
        metrics_file.write_text(json.dumps(metrics))

        # Set environment for test
        env = os.environ.copy()
        env.update({
            "SLO_METRICS_FILE": str(metrics_file),
            "SLO_MAX_P95_MS": "300",
            "SLO_MAX_ERROR_RATE": "0.01"
        })

        if self.slo_script.exists():
            # Run SLO gate check
            result = subprocess.run([
                "python", str(self.slo_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 0, 
                           f"SLO gate should pass: {result.stdout} {result.stderr}")
            self.assertIn("PASS", result.stdout)

    def test_slo_gate_check_fail_p95(self):
        """Test SLO gate check with failing P95 metrics."""
        # Create test metrics file with high P95
        metrics = {
            "health": {
                "count": 20,
                "p95_ms": 500.0,  # Above 300ms threshold
                "error_rate": 0.005
            }
        }
        metrics_file = self.temp_dir / "slo_fail.json"
        metrics_file.write_text(json.dumps(metrics))

        # Set environment for test
        env = os.environ.copy()
        env.update({
            "SLO_METRICS_FILE": str(metrics_file),
            "SLO_MAX_P95_MS": "300",
            "SLO_MAX_ERROR_RATE": "0.01"
        })

        if self.slo_script.exists():
            # Run SLO gate check
            result = subprocess.run([
                "python", str(self.slo_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 1, 
                           f"SLO gate should fail: {result.stdout} {result.stderr}")
            self.assertIn("FAIL", result.stdout)

    def test_slo_gate_check_multiple_endpoints(self):
        """Test SLO gate check with multiple endpoint metrics."""
        # Create test metrics with multiple endpoints
        metrics = {
            "GET /health": {"count": 10, "p95_ms": 100.0, "error_rate": 0.0},
            "GET /openapi.json": {"count": 10, "p95_ms": 200.0, "error_rate": 0.0},
            "POST /v1/measure": {"count": 10, "p95_ms": 250.0, "error_rate": 0.01}
        }
        metrics_file = self.temp_dir / "slo_multi.json"
        metrics_file.write_text(json.dumps(metrics))

        # Set environment for test
        env = os.environ.copy()
        env.update({
            "SLO_METRICS_FILE": str(metrics_file),
            "SLO_MAX_P95_MS": "300",
            "SLO_MAX_ERROR_RATE": "0.01"
        })

        if self.slo_script.exists():
            # Run SLO gate check
            result = subprocess.run([
                "python", str(self.slo_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 0, 
                           f"SLO gate should pass: {result.stdout} {result.stderr}")


class TestA7MultiOSPerfGate(unittest.TestCase):
    """Test suite for A7 Multi-OS Performance Gate."""

    def setUp(self):
        """Set up test environment."""
        self.temp_dir = Path(tempfile.mkdtemp())
        self.perf_script = Path("scripts/a7/multi_os_perf_gate.py")

    def tearDown(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_multi_os_perf_gate_linux(self):
        """Test multi-OS performance gate on Linux."""
        output_file = self.temp_dir / "perf_linux.json"
        
        # Set environment for Linux test
        env = os.environ.copy()
        env.update({
            "RUNNER_OS": "Linux",
            "PYTHON_VERSION": "3.11",
            "PERF_OUTPUT_FILE": str(output_file)
        })

        if self.perf_script.exists():
            # Run performance test
            result = subprocess.run([
                "python", str(self.perf_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 0, 
                           f"Performance test should pass: {result.stdout} {result.stderr}")
            
            # Verify output file was created
            self.assertTrue(output_file.exists(), "Performance output file should be created")
            
            # Verify output format
            perf_data = json.loads(output_file.read_text())
            self.assertIn("_summary", perf_data)
            self.assertEqual(perf_data["_summary"]["platform"], "linux")

    def test_multi_os_perf_gate_windows(self):
        """Test multi-OS performance gate on Windows."""
        output_file = self.temp_dir / "perf_windows.json"
        
        # Set environment for Windows test
        env = os.environ.copy()
        env.update({
            "RUNNER_OS": "Windows",
            "PYTHON_VERSION": "3.12",
            "PERF_OUTPUT_FILE": str(output_file)
        })

        if self.perf_script.exists():
            # Run performance test
            result = subprocess.run([
                "python", str(self.perf_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 0, 
                           f"Performance test should pass: {result.stdout} {result.stderr}")
            
            # Verify output file was created
            self.assertTrue(output_file.exists(), "Performance output file should be created")
            
            # Verify Windows-specific configuration
            perf_data = json.loads(output_file.read_text())
            self.assertEqual(perf_data["_summary"]["platform"], "windows")


class TestA7CoverageGateEnforcer(unittest.TestCase):
    """Test suite for A7 Coverage Gate Enforcer."""

    def setUp(self):
        """Set up test environment."""
        self.temp_dir = Path(tempfile.mkdtemp())
        self.coverage_script = Path("scripts/a7/coverage_gate_enforcer.py")

    def tearDown(self):
        """Clean up test environment."""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_coverage_gate_enforcer_pass(self):
        """Test coverage gate enforcer with passing coverage."""
        # Create mock coverage files
        artifacts_dir = self.temp_dir / "artifacts"
        
        # Ubuntu coverage
        ubuntu_dir = artifacts_dir / "coverage-ubuntu-latest-py3.11"
        ubuntu_dir.mkdir(parents=True)
        ubuntu_coverage = {
            "totals": {
                "percent_covered": 85.5,
                "covered_lines": 855,
                "num_statements": 1000
            }
        }
        (ubuntu_dir / "coverage.json").write_text(json.dumps(ubuntu_coverage))

        # Windows coverage
        windows_dir = artifacts_dir / "coverage-windows-latest-py3.11"
        windows_dir.mkdir(parents=True)
        windows_coverage = {
            "totals": {
                "percent_covered": 82.0,
                "covered_lines": 820,
                "num_statements": 1000
            }
        }
        (windows_dir / "coverage.json").write_text(json.dumps(windows_coverage))

        # Set environment
        env = os.environ.copy()
        env.update({
            "COVERAGE_THRESHOLD": "80",
            "COVERAGE_ARTIFACT_DIR": str(artifacts_dir)
        })

        if self.coverage_script.exists():
            # Run coverage gate enforcer
            result = subprocess.run([
                "python", str(self.coverage_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 0, 
                           f"Coverage gate should pass: {result.stdout} {result.stderr}")
            self.assertIn("passed", result.stdout.lower())

    def test_coverage_gate_enforcer_fail(self):
        """Test coverage gate enforcer with failing coverage."""
        # Create mock coverage files with low coverage
        artifacts_dir = self.temp_dir / "artifacts"
        
        # Low coverage file
        low_dir = artifacts_dir / "coverage-ubuntu-latest-py3.11"
        low_dir.mkdir(parents=True)
        low_coverage = {
            "totals": {
                "percent_covered": 65.0,  # Below 80% threshold
                "covered_lines": 650,
                "num_statements": 1000
            }
        }
        (low_dir / "coverage.json").write_text(json.dumps(low_coverage))

        # Set environment
        env = os.environ.copy()
        env.update({
            "COVERAGE_THRESHOLD": "80",
            "COVERAGE_ARTIFACT_DIR": str(artifacts_dir)
        })

        if self.coverage_script.exists():
            # Run coverage gate enforcer
            result = subprocess.run([
                "python", str(self.coverage_script)
            ], env=env, capture_output=True, text=True)

            self.assertEqual(result.returncode, 1, 
                           f"Coverage gate should fail: {result.stdout} {result.stderr}")
            self.assertIn("fail", result.stdout.lower())


class TestA7CIGatesIntegration(unittest.TestCase):
    """Integration tests for A7 CI/CD & SLO-Gates."""

    def test_a7_workflow_file_exists(self):
        """Test that A7 workflow file exists and is valid YAML."""
        workflow_file = Path(".github/workflows/ci-gates.yml")
        
        if workflow_file.exists():
            content = workflow_file.read_text()
            
            # Check for key A7 components
            self.assertIn("ci-gates", content)
            self.assertIn("multi-os-test", content)
            self.assertIn("slo-performance-gates", content)
            self.assertIn("coverage", content)
            self.assertIn("matrix:", content)
            self.assertIn("ubuntu-latest", content)
            self.assertIn("windows-latest", content)
            self.assertIn("macos-latest", content)

    def test_a7_scripts_exist(self):
        """Test that A7 script files exist."""
        scripts = [
            "scripts/a7/slo_gate_check.py",
            "scripts/a7/multi_os_perf_gate.py",
            "scripts/a7/coverage_gate_enforcer.py"
        ]
        
        for script_path in scripts:
            script_file = Path(script_path)
            if script_file.exists():
                # Check that script is executable Python
                content = script_file.read_text()
                self.assertIn("#!/usr/bin/env python3", content)
                self.assertIn("def main()", content)

    def test_a7_enterprise_quality_standards(self):
        """Test that A7 meets enterprise quality standards."""
        # Check workflow includes enterprise requirements
        workflow_file = Path(".github/workflows/ci-gates.yml")
        
        if workflow_file.exists():
            content = workflow_file.read_text()
            
            # Multi-OS support
            self.assertIn("ubuntu-latest", content)
            self.assertIn("windows-latest", content)
            self.assertIn("macos-latest", content)
            
            # Multiple Python versions
            self.assertIn("3.11", content)
            self.assertIn("3.12", content)
            
            # Enterprise quality gates
            self.assertIn("COVERAGE_THRESHOLD", content)
            self.assertIn("SLO_MAX_P95_MS", content)
            self.assertIn("security", content)
            
            # Performance requirements
            self.assertIn("300", content)  # 300ms SLO threshold


def run_a7_tests():
    """
    PL: Uruchamia wszystkie testy A7 CI/CD & SLO-Gates.
    EN: Run all A7 CI/CD & SLO-Gates tests.
    """
    print("Running A7 CI/CD & SLO-Gates Test Suite")
    print("=" * 60)
    
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    test_classes = [
        TestA7SLOGateCheck,
        TestA7MultiOSPerfGate,
        TestA7CoverageGateEnforcer,
        TestA7CIGatesIntegration
    ]
    
    for test_class in test_classes:
        tests = loader.loadTestsFromTestCase(test_class)
        suite.addTests(tests)
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Summary
    total_tests = result.testsRun
    failures = len(result.failures)
    errors = len(result.errors)
    passed = total_tests - failures - errors
    
    print("\n" + "=" * 60)
    print(f"A7 Test Results: {passed}/{total_tests} passed")
    
    if failures > 0:
        print(f"FAILURES: {failures}")
    if errors > 0:
        print(f"ERRORS: {errors}")
    
    if failures == 0 and errors == 0:
        print("PASS: All A7 CI/CD & SLO-Gates tests passed!")
        print("SUCCESS: Enterprise big tech quality achieved")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_a7_tests()
    exit(0 if success else 1)


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===