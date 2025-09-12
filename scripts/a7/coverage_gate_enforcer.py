#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/a7/coverage_gate_enforcer.py                 |
# | ROLE: A7 CI/CD Coverage Gate - Enterprise Quality Control  |
# | DESC: Multi-OS coverage validation with configurable limits|
# +-------------------------------------------------------------+

import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


def parse_coverage_json(coverage_file: str) -> Optional[Dict[str, Any]]:
    """
    PL: Parsuje plik coverage.json i wyciąga metryki pokrycia.
    EN: Parse coverage.json file and extract coverage metrics.
    
    Args:
        coverage_file: Path to coverage.json file
    
    Returns:
        Coverage data dictionary or None if failed
    """
    try:
        coverage_path = Path(coverage_file)
        if not coverage_path.exists():
            print(f"Coverage file not found: {coverage_file}")
            return None
            
        data = json.loads(coverage_path.read_text(encoding='utf-8'))
        return data
        
    except Exception as e:
        print(f"Failed to parse coverage file: {e}")
        return None


def extract_coverage_percentage(coverage_data: Dict[str, Any]) -> float:
    """
    PL: Wyciąga procent pokrycia z danych coverage.
    EN: Extract coverage percentage from coverage data.
    
    Args:
        coverage_data: Coverage data dictionary
    
    Returns:
        Coverage percentage (0.0-100.0)
    """
    try:
        # Standard coverage.py format
        if 'totals' in coverage_data:
            totals = coverage_data['totals']
            if 'percent_covered' in totals:
                return float(totals['percent_covered'])
            elif 'percent_covered_display' in totals:
                # Remove '%' if present
                percent_str = str(totals['percent_covered_display']).rstrip('%')
                return float(percent_str)
        
        # Alternative format - summary
        if 'summary' in coverage_data:
            summary = coverage_data['summary']
            if 'percent_covered' in summary:
                return float(summary['percent_covered'])
        
        # Calculate from line counts
        if 'totals' in coverage_data:
            totals = coverage_data['totals']
            covered = totals.get('covered_lines', 0)
            total = totals.get('num_statements', 0)
            if total > 0:
                return (covered / total) * 100
        
        # Last resort - look for any percentage field
        for key, value in coverage_data.items():
            if 'percent' in key.lower() and isinstance(value, (int, float)):
                return float(value)
        
        print("Could not extract coverage percentage from data")
        return 0.0
        
    except Exception as e:
        print(f"Error extracting coverage percentage: {e}")
        return 0.0


def check_coverage_threshold(coverage_files: List[str], threshold: float) -> bool:
    """
    PL: Sprawdza czy pokrycie kodu przekracza próg dla wszystkich platform.
    EN: Check if code coverage exceeds threshold for all platforms.
    
    Args:
        coverage_files: List of coverage file paths
        threshold: Minimum coverage percentage required
    
    Returns:
        True if all coverage files meet threshold
    """
    print(f"Coverage threshold: >={threshold}%")
    print("=" * 40)
    
    all_passed = True
    coverage_results = []
    
    for coverage_file in coverage_files:
        print(f"Checking: {coverage_file}")
        
        # Parse coverage data
        coverage_data = parse_coverage_json(coverage_file)
        if coverage_data is None:
            print("   Failed to parse coverage file")
            all_passed = False
            continue
        
        # Extract percentage
        coverage_percent = extract_coverage_percentage(coverage_data)
        
        # Check threshold
        passed = coverage_percent >= threshold
        status = "PASS" if passed else "FAIL"
        
        print(f"   {status} Coverage: {coverage_percent:.1f}%")
        
        coverage_results.append({
            "file": coverage_file,
            "coverage": coverage_percent,
            "passed": passed
        })
        
        if not passed:
            all_passed = False    # Summary
    print("=" * 40)
    print("Coverage Summary:")
    
    if coverage_results:
        total_coverage = sum(r['coverage'] for r in coverage_results) / len(coverage_results)
        passed_count = sum(1 for r in coverage_results if r['passed'])
        
        print(f"   Average Coverage: {total_coverage:.1f}%")
        print(f"   Platforms Passed: {passed_count}/{len(coverage_results)}")
        
        if all_passed:
            print("   All platforms meet coverage requirements")
        else:
            print("   Some platforms below coverage threshold")
            print(f"   Required: >={threshold}%")
    
    return all_passed


def discover_coverage_files(artifact_dir: str) -> List[str]:
    """
    PL: Automatycznie znajduje pliki coverage w katalogach artefaktów.
    EN: Automatically discover coverage files in artifact directories.
    
    Args:
        artifact_dir: Base artifact directory
    
    Returns:
        List of discovered coverage file paths
    """
    coverage_files = []
    artifact_path = Path(artifact_dir)
    
    if not artifact_path.exists():
        print(f"Artifact directory not found: {artifact_dir}")
        return coverage_files
    
    # Look for coverage files in subdirectories
    for item in artifact_path.iterdir():
        if item.is_dir() and 'coverage-' in item.name:
            coverage_json = item / 'coverage.json'
            if coverage_json.exists():
                coverage_files.append(str(coverage_json))
                print(f"Found coverage file: {coverage_json}")
    
    # Also check for direct coverage.json files
    direct_coverage = artifact_path / 'coverage.json'
    if direct_coverage.exists():
        coverage_files.append(str(direct_coverage))
        print(f"Found direct coverage file: {direct_coverage}")
    
    return coverage_files


def main() -> int:
    """Main entry point for coverage gate enforcer."""
    # Configuration from environment
    threshold = float(os.environ.get('COVERAGE_THRESHOLD', '80'))
    artifact_dir = os.environ.get('COVERAGE_ARTIFACT_DIR', 'artifacts')
    coverage_files_env = os.environ.get('COVERAGE_FILES', '')
    
    print("A7 Coverage Gate Enforcer")
    print("=" * 50)
    
    # Determine coverage files to check
    if coverage_files_env:
        # Explicit file list from environment
        coverage_files = [f.strip() for f in coverage_files_env.split(',') if f.strip()]
        print(f"Using explicit coverage files: {len(coverage_files)} files")
    else:
        # Auto-discover from artifacts
        coverage_files = discover_coverage_files(artifact_dir)
        print(f"Auto-discovered coverage files: {len(coverage_files)} files")
    
    if not coverage_files:
        print("WARNING: No coverage files found - skipping coverage gate")
        return 0
    
    # Run coverage check
    success = check_coverage_threshold(coverage_files, threshold)
    
    if success:
        print("\nPASS: Coverage gate passed - all platforms meet requirements")
        return 0
    else:
        print("\nFAIL: Coverage gate failed - insufficient coverage on some platforms")
        return 1


if __name__ == "__main__":
    sys.exit(main())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===