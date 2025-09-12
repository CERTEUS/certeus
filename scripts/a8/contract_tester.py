#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/a8/contract_tester.py                        |
# | ROLE: A8 OpenAPI contract testing framework                |
# | PLIK: scripts/a8/contract_tester.py                        |
# | ROLA: A8 framework testowania kontraktów OpenAPI           |
# +-------------------------------------------------------------+
"""
PL: Framework testowania kontraktów API na bazie OpenAPI z Schemathesis.
EN: OpenAPI contract testing framework using Schemathesis.
"""

# === IMPORTY / IMPORTS ===

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

# === KONFIGURACJA / CONFIGURATION ===

REPO_ROOT = Path(__file__).resolve().parents[2]
REPORTS_DIR = REPO_ROOT / "reports" / "a8"
OPENAPI_SPEC_PATH = REPO_ROOT / "docs" / "api" / "openapi.yaml"

# === MODELE / MODELS ===

class ContractTestResult:
    """Contract test result container."""
    
    def __init__(self):
        self.total_tests = 0
        self.passed_tests = 0
        self.failed_tests = 0
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self.execution_time = 0.0
        self.coverage_percentage = 0.0

class ContractTester:
    """Enterprise API contract testing framework."""
    
    def __init__(self, base_url: str = "http://127.0.0.1:8000"):
        self.base_url = base_url.rstrip("/")
        self.reports_dir = REPORTS_DIR
        self.spec_path = OPENAPI_SPEC_PATH
        self.result = ContractTestResult()
        
    def ensure_reports_directory(self) -> None:
        """Ensure reports directory exists."""
        self.reports_dir.mkdir(parents=True, exist_ok=True)
        print(f"Reports directory: {self.reports_dir}")
    
    def validate_openapi_spec(self) -> bool:
        """Validate OpenAPI specification."""
        print("Validating OpenAPI specification...")
        
        try:
            # Check if spec file exists
            if not self.spec_path.exists():
                self.result.errors.append(f"OpenAPI spec not found: {self.spec_path}")
                return False
            
            # Try to parse YAML/JSON
            if self.spec_path.suffix == '.yaml':
                import yaml
                with open(self.spec_path, 'r', encoding='utf-8') as f:
                    spec = yaml.safe_load(f)
            else:
                with open(self.spec_path, 'r', encoding='utf-8') as f:
                    spec = json.load(f)
            
            # Basic validation
            required_fields = ['openapi', 'info', 'paths']
            for field in required_fields:
                if field not in spec:
                    self.result.errors.append(f"Missing required field in OpenAPI spec: {field}")
                    return False
            
            paths = spec.get('paths', {})
            if not paths:
                self.result.warnings.append("No paths defined in OpenAPI spec")
            
            print(f"OpenAPI spec validation: PASS ({len(paths)} paths)")
            return True
            
        except Exception as e:
            self.result.errors.append(f"Failed to validate OpenAPI spec: {e}")
            return False
    
    def check_api_health(self) -> bool:
        """Check if API is responsive."""
        print(f"Checking API health at: {self.base_url}")
        
        try:
            import urllib.error
            import urllib.request

            # Test health endpoint
            health_url = f"{self.base_url}/health"
            req = urllib.request.Request(health_url)
            
            with urllib.request.urlopen(req, timeout=10) as response:
                if response.status == 200:
                    health_data = json.loads(response.read().decode('utf-8'))
                    print(f"API health check: PASS (status: {health_data.get('status', 'unknown')})")
                    return True
                else:
                    self.result.errors.append(f"Health check failed: HTTP {response.status}")
                    return False
        
        except Exception as e:
            self.result.errors.append(f"API health check failed: {e}")
            return False
    
    def run_schemathesis_tests(self) -> bool:
        """Run Schemathesis contract tests."""
        print("Running Schemathesis contract tests...")
        
        try:
            # Check if schemathesis is available
            result = subprocess.run(['python', '-c', 'import schemathesis'], 
                                  capture_output=True, text=True)
            
            if result.returncode != 0:
                self.result.warnings.append("Schemathesis not available, installing...")
                # Try to install schemathesis
                install_result = subprocess.run([
                    'python', '-m', 'pip', 'install', 'schemathesis'
                ], capture_output=True, text=True)
                
                if install_result.returncode != 0:
                    self.result.errors.append("Failed to install Schemathesis")
                    return False
            
            # Prepare Schemathesis command
            output_file = self.reports_dir / "schemathesis_report.json"
            
            cmd = [
                'python', '-m', 'schemathesis', 'run',
                str(self.spec_path),
                '--base-url', self.base_url,
                '--report', str(output_file),
                '--checks', 'all',
                '--workers', '1',
                '--max-examples', '10',
                '--timeout', '30'
            ]
            
            # Run Schemathesis
            print(f"Executing: {' '.join(cmd)}")
            start_time = time.time()
            
            result = subprocess.run(cmd, capture_output=True, text=True)
            self.result.execution_time = time.time() - start_time
            
            # Parse results
            if output_file.exists():
                with open(output_file, 'r', encoding='utf-8') as f:
                    report_data = json.load(f)
                    self._parse_schemathesis_report(report_data)
            
            if result.returncode == 0:
                print("Schemathesis tests: PASS")
                return True
            else:
                self.result.errors.append(f"Schemathesis tests failed: {result.stderr}")
                print(f"Schemathesis tests: FAIL - {result.stderr}")
                return False
            
        except Exception as e:
            self.result.errors.append(f"Failed to run Schemathesis tests: {e}")
            return False
    
    def _parse_schemathesis_report(self, report_data: Dict[str, Any]) -> None:
        """Parse Schemathesis JSON report."""
        try:
            # Extract test statistics
            self.result.total_tests = report_data.get('total', {}).get('total', 0)
            self.result.passed_tests = report_data.get('total', {}).get('passed', 0)
            self.result.failed_tests = report_data.get('total', {}).get('failed', 0)
            
            # Calculate coverage
            if self.result.total_tests > 0:
                self.result.coverage_percentage = (self.result.passed_tests / self.result.total_tests) * 100
            
            # Extract failures
            failures = report_data.get('results', [])
            for failure in failures:
                if failure.get('check') == 'not_a_server_error':
                    self.result.errors.append(f"Server error on {failure.get('method')} {failure.get('path')}")
                elif failure.get('check') == 'response_schema_conformance':
                    self.result.errors.append(f"Schema validation failed on {failure.get('method')} {failure.get('path')}")
        
        except Exception as e:
            self.result.warnings.append(f"Failed to parse Schemathesis report: {e}")
    
    def run_custom_contract_tests(self) -> bool:
        """Run custom contract validation tests with retry logic."""
        print("Running custom contract tests...")
        
        try:
            # Test critical endpoints manually with retry
            critical_endpoints = [
                ('GET', '/health'),
                ('GET', '/openapi.json'),
                ('GET', '/.well-known/jwks.json'),
            ]
            
            custom_passed = 0
            custom_total = len(critical_endpoints)
            max_retries = 3
            retry_delay = 1.0
            
            import time
            import urllib.error
            import urllib.request
            
            for method, path in critical_endpoints:
                success = False
                last_error = None
                
                for attempt in range(max_retries):
                    try:
                        url = f"{self.base_url}{path}"
                        req = urllib.request.Request(url, method=method)
                        
                        with urllib.request.urlopen(req, timeout=10) as response:
                            if 200 <= response.status < 300:
                                custom_passed += 1
                                print(f"  PASS: {method} {path}")
                                success = True
                                break
                            else:
                                last_error = f"Status {response.status}"
                                if attempt < max_retries - 1:
                                    print(f"  RETRY {attempt + 1}: {method} {path} -> Status {response.status}")
                                    time.sleep(retry_delay)
                    
                    except Exception as e:
                        last_error = str(e)
                        if attempt < max_retries - 1:
                            print(f"  RETRY {attempt + 1}: {method} {path} -> {e}")
                            time.sleep(retry_delay)
                
                if not success:
                    self.result.errors.append(f"Custom test failed: {method} {path} -> {last_error}")
                    print(f"  ERROR: {method} {path} -> {last_error}")
            
            # Update totals
            self.result.total_tests += custom_total
            self.result.passed_tests += custom_passed
            self.result.failed_tests += (custom_total - custom_passed)
            
            print(f"Custom contract tests: {custom_passed}/{custom_total} passed")
            return custom_passed == custom_total
            
        except Exception as e:
            self.result.errors.append(f"Failed to run custom contract tests: {e}")
            return False
    
    def generate_report(self) -> None:
        """Generate comprehensive test report."""
        print("\nGenerating contract test report...")
        
        # Generate JSON report
        report_data = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime()),
            'base_url': self.base_url,
            'spec_path': str(self.spec_path),
            'summary': {
                'total_tests': self.result.total_tests,
                'passed_tests': self.result.passed_tests,
                'failed_tests': self.result.failed_tests,
                'success_rate': round((self.result.passed_tests / max(self.result.total_tests, 1)) * 100, 2),
                'execution_time_seconds': round(self.result.execution_time, 2),
                'coverage_percentage': round(self.result.coverage_percentage, 2)
            },
            'errors': self.result.errors,
            'warnings': self.result.warnings,
            'status': 'PASS' if not self.result.errors and self.result.failed_tests == 0 else 'FAIL'
        }
        
        # Save JSON report
        json_report_file = self.reports_dir / "contract_test_report.json"
        with open(json_report_file, 'w', encoding='utf-8') as f:
            json.dump(report_data, f, indent=2)
        
        print(f"JSON report saved: {json_report_file}")
        
        # Generate markdown report
        md_report = self._generate_markdown_report(report_data)
        md_report_file = self.reports_dir / "contract_test_report.md"
        
        with open(md_report_file, 'w', encoding='utf-8') as f:
            f.write(md_report)
        
        print(f"Markdown report saved: {md_report_file}")
    
    def _generate_markdown_report(self, report_data: Dict[str, Any]) -> str:
        """Generate markdown test report."""
        summary = report_data['summary']
        status_icon = 'PASS' if report_data['status'] == 'PASS' else 'FAIL'
        
        md_content = f"""# A8 Contract Testing Report

## Executive Summary
**Status: {status_icon}**
- **Test Timestamp**: {report_data['timestamp']}
- **API Base URL**: {report_data['base_url']}
- **OpenAPI Spec**: {report_data['spec_path']}

## Test Results
| Metric | Value |
|--------|-------|
| Total Tests | {summary['total_tests']} |
| Passed Tests | {summary['passed_tests']} |
| Failed Tests | {summary['failed_tests']} |
| Success Rate | {summary['success_rate']}% |
| Execution Time | {summary['execution_time_seconds']}s |
| Coverage | {summary['coverage_percentage']}% |

## Quality Gates
"""

        # Quality gate assessment
        if summary['success_rate'] >= 95:
            md_content += "- SUCCESS: Success rate >= 95%\n"
        else:
            md_content += f"- FAIL: Success rate {summary['success_rate']}% < 95%\n"
        
        if summary['execution_time_seconds'] <= 60:
            md_content += "- SUCCESS: Execution time <= 60s\n"
        else:
            md_content += f"- FAIL: Execution time {summary['execution_time_seconds']}s > 60s\n"
        
        if not report_data['errors']:
            md_content += "- SUCCESS: No critical errors\n"
        else:
            md_content += f"- FAIL: {len(report_data['errors'])} critical errors found\n"
        
        # Errors section
        if report_data['errors']:
            md_content += "\n## Errors\n"
            for i, error in enumerate(report_data['errors'], 1):
                md_content += f"{i}. {error}\n"
        
        # Warnings section
        if report_data['warnings']:
            md_content += "\n## Warnings\n"
            for i, warning in enumerate(report_data['warnings'], 1):
                md_content += f"{i}. {warning}\n"
        
        md_content += f"""
## Recommendations

### For Success Rate < 95%
- Review failed endpoint implementations
- Validate OpenAPI schema definitions
- Check response format compliance

### For High Execution Time
- Optimize endpoint response times
- Review database query performance
- Consider implementing response caching

### For Schema Validation Errors
- Ensure response schemas match OpenAPI definitions
- Validate request/response examples
- Update OpenAPI spec if API behavior is correct

## Enterprise Standards Compliance
- Contract Testing: {'PASS' if summary['success_rate'] >= 95 else 'FAIL'}
- Performance SLA: {'PASS' if summary['execution_time_seconds'] <= 60 else 'FAIL'}
- Error Handling: {'PASS' if not report_data['errors'] else 'FAIL'}
- Documentation Sync: {'PASS' if summary['coverage_percentage'] >= 80 else 'FAIL'}

**Overall Assessment: {report_data['status']}**
"""
        
        return md_content

# === LOGIKA / LOGIC ===

def main() -> int:
    """Main entry point for A8 contract tester."""
    print("A8 Contract Tester - Enterprise API Validation")
    print("=" * 60)
    
    # Parse command line arguments
    base_url = os.getenv('API_BASE_URL', 'http://127.0.0.1:8000')
    if len(sys.argv) > 1:
        base_url = sys.argv[1]
    
    print(f"Target API: {base_url}")
    
    # Initialize contract tester
    tester = ContractTester(base_url)
    tester.ensure_reports_directory()
    
    # Run validation steps
    steps_passed = 0
    total_steps = 4
    
    # Step 1: Validate OpenAPI spec
    if tester.validate_openapi_spec():
        steps_passed += 1
    
    # Step 2: Check API health
    if tester.check_api_health():
        steps_passed += 1
    
    # Step 3: Run Schemathesis tests
    if tester.run_schemathesis_tests():
        steps_passed += 1
    
    # Step 4: Run custom contract tests
    if tester.run_custom_contract_tests():
        steps_passed += 1
    
    # Generate comprehensive report
    tester.generate_report()
    
    # Print summary
    print("\n" + "=" * 60)
    print(f"A8 Contract Testing Summary:")
    print(f"  Validation Steps: {steps_passed}/{total_steps} passed")
    print(f"  API Tests: {tester.result.passed_tests}/{tester.result.total_tests} passed")
    print(f"  Success Rate: {(tester.result.passed_tests / max(tester.result.total_tests, 1)) * 100:.1f}%")
    print(f"  Execution Time: {tester.result.execution_time:.1f}s")
    
    if tester.result.errors:
        print(f"  Critical Errors: {len(tester.result.errors)}")
        for error in tester.result.errors[:3]:  # Show first 3 errors
            print(f"    - {error}")
    
    # Determine exit code
    success = (steps_passed == total_steps and 
              tester.result.failed_tests == 0 and 
              not tester.result.errors)
    
    if success:
        print("\nPASS: All contract tests passed - Enterprise quality achieved")
        return 0
    else:
        print("\nFAIL: Contract testing failed - Review errors and warnings")
        return 1

if __name__ == "__main__":
    sys.exit(main())

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===