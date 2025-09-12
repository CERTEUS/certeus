#!/usr/bin/env python3
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/a7/slo_gate_check.py                         |
# | ROLE: A7 CI/CD SLO Gate - Performance threshold checker    |
# | DESC: Enterprise SLO enforcement with configurable limits  |
# +-------------------------------------------------------------+

import json
import os
from pathlib import Path
import sys
from typing import Any


def check_slo_metrics(metrics_file: str, max_p95_ms: float, max_error_rate: float) -> bool:
    """
    PL: Sprawdza czy metryki SLO mieszczą się w dopuszczalnych progach.
    EN: Check if SLO metrics are within acceptable thresholds.

    Args:
        metrics_file: Path to JSON file with SLO metrics
        max_p95_ms: Maximum allowed p95 latency in milliseconds
        max_error_rate: Maximum allowed error rate (0.0-1.0)

    Returns:
        True if SLO passed, False otherwise
    """
    try:
        metrics_path = Path(metrics_file)
        if not metrics_path.exists():
            print(f"SLO metrics file not found: {metrics_file}")
            return False

        data: dict[str, Any] = json.loads(metrics_path.read_text(encoding='utf-8'))

        # Support different metric formats
        if 'health' in data:
            # Format: {"health": {"p95_ms": 150.0, "error_rate": 0.0}}
            health_data = data['health']
            p95_ms = float(health_data.get('p95_ms', 0))
            error_rate = float(health_data.get('error_rate', 0))
        elif 'p95_ms' in data:
            # Format: {"p95_ms": 150.0, "error_rate": 0.0}
            p95_ms = float(data.get('p95_ms', 0))
            error_rate = float(data.get('error_rate', 0))
        else:
            # Try to find metrics in nested structure
            p95_ms = 0
            error_rate = 0
            for _endpoint, stats in data.items():
                if isinstance(stats, dict):
                    endpoint_p95 = float(stats.get('p95_ms', 0))
                    endpoint_err = float(stats.get('error_rate', 0))
                    p95_ms = max(p95_ms, endpoint_p95)  # Use worst case
                    error_rate = max(error_rate, endpoint_err)

        # Check thresholds
        p95_ok = p95_ms <= max_p95_ms
        err_ok = error_rate <= max_error_rate
        overall_ok = p95_ok and err_ok

        # Report results
        p95_status = "PASS" if p95_ok else "FAIL"
        err_status = "PASS" if err_ok else "FAIL"
        overall_status = "PASS" if overall_ok else "FAIL"

        print("SLO Gate Results:")
        print(f"   P95 Latency: {p95_ms:.2f}ms (limit: {max_p95_ms}ms) - {p95_status}")
        print(f"   Error Rate: {error_rate:.4f} (limit: {max_error_rate}) - {err_status}")
        print(f"   Overall: {overall_status}")

        if not overall_ok:
            print("SLO thresholds exceeded - failing gate")

        return overall_ok

    except Exception as e:
        print(f"SLO check failed with error: {e}")
        return False


def main() -> int:
    """Main entry point for SLO gate check."""
    # Get configuration from environment
    metrics_file = os.environ.get('SLO_METRICS_FILE', 'out/endpoint_slo.json')
    max_p95_ms = float(os.environ.get('SLO_MAX_P95_MS', '300'))
    max_error_rate = float(os.environ.get('SLO_MAX_ERROR_RATE', '0.01'))

    print(f"Checking SLO metrics from: {metrics_file}")
    print(f"Thresholds: P95 <= {max_p95_ms}ms, Error Rate <= {max_error_rate}")

    # Run SLO check
    success = check_slo_metrics(metrics_file, max_p95_ms, max_error_rate)

    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
