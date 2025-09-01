"""
PL: Moduł projektu CERTEUS (uogólniony opis).

EN: CERTEUS project module (generic description).
"""

# === IMPORTY / IMPORTS ===
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import xml.etree.ElementTree as ET

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===


# +=====================================================================+

# |                              CERTEUS                                |

# +=====================================================================+

# | FILE: scripts/compute_truth_gates.py                                 |

# | ROLE:                                                                |

# |  PL: Oblicza bramki prawdy AFV/ASE/ATC na bazie metryk CI i zapisuje |

# |      JSON (reports/junit.xml, out/gates & SLO).                      |

# |  EN: Computes Truth Gates AFV/ASE/ATC from CI metrics and writes JSON|

# +=====================================================================+


def _read_json(p: Path):
    try:
        return json.loads(p.read_text(encoding="utf-8"))

    except Exception:
        return None


def _parse_junit(p: Path) -> dict:
    if not p.exists():
        return {"total": 0, "failures": 0, "errors": 0, "skipped": 0}

    try:
        root = ET.fromstring(p.read_text(encoding="utf-8"))

        # Handle <testsuite> root or <testsuites>

        suites = []

        if root.tag == "testsuite":
            suites = [root]

        else:
            suites = list(root.findall("testsuite"))

        total = sum(int(s.get("tests", 0)) for s in suites)

        failures = sum(int(s.get("failures", 0)) for s in suites)

        errors = sum(int(s.get("errors", 0)) for s in suites)

        skipped = sum(int(s.get("skipped", 0)) for s in suites)

        return {"total": total, "failures": failures, "errors": errors, "skipped": skipped}

    except Exception:
        return {"total": 0, "failures": 1, "errors": 0, "skipped": 0}


def main() -> int:
    ap = argparse.ArgumentParser()

    ap.add_argument("--out", required=True, help="output file path (JSON)")

    args = ap.parse_args()

    out = Path(args.out)

    out.parent.mkdir(parents=True, exist_ok=True)

    junit = _parse_junit(Path("reports/junit.xml"))

    slo = _read_json(Path("out/slo_metrics.json")) or {}

    gauge = _read_json(Path("out/gauge.json")) or {}

    cov = _read_json(Path("out/lexqft_coverage.json")) or {}

    boundary = _read_json(Path("out/boundary_report.json")) or {}

    # Thresholds

    eps = float(os.getenv("GAUGE_EPSILON", "1e-3"))

    cov_min = float(os.getenv("PATH_COV_MIN_GAMMA", "0.90"))

    unc_max = float(os.getenv("PATH_COV_MAX_UNCAPTURED", "0.05"))

    p95_max = float(os.getenv("SLO_MAX_P95_MS", "250"))

    err_max = float(os.getenv("SLO_MAX_ERROR_RATE", "0.005"))

    tests_ok = (junit.get("failures", 0) + junit.get("errors", 0)) == 0 and junit.get("total", 0) > 0

    slo_p95 = float(((slo or {}).get("latency_ms", {}) or {}).get("p95", 0.0))

    slo_err = float((slo or {}).get("error_rate", 0.0))

    slo_ok = slo_p95 <= p95_max and slo_err <= err_max

    gauge_ok = float(((gauge or {}).get("gauge", {}) or {}).get("holonomy_drift", 1.0)) <= eps

    cov_gamma = float((cov or {}).get("coverage_gamma", 0.0))

    cov_unc = float((cov or {}).get("uncaptured_mass", 1.0))

    cov_ok = (cov_gamma >= cov_min) and (cov_unc <= unc_max)

    bdy_ok = int(((boundary or {}).get("boundary", {}) or {}).get("delta_bits", 1)) == 0

    AFV = {
        "status": "PASS" if (tests_ok and gauge_ok and cov_ok and bdy_ok) else "FAIL",
        "tests": junit,
        "gauge": gauge,
        "path_coverage": cov,
        "boundary": boundary,
    }

    ASE = {
        "status": "PASS" if slo_ok else "FAIL",
        "slo": {"p95_max": p95_max, "error_max": err_max, "measured": {"p95": slo_p95, "error": slo_err}},
    }

    cosign_v = _read_json(Path("out/cosign_verify.json")) or {}

    cosign_ok = bool(cosign_v.get("results")) and all(r.get("verified") for r in cosign_v.get("results", []))

    ATC = {
        "status": "PASS"
        if (Path("sbom.json").exists() and Path("out/provenance.json").exists() and cosign_ok)
        else ("WARN" if Path("sbom.json").exists() and Path("out/provenance.json").exists() else "FAIL"),
        "artifacts": {
            "sbom": Path("sbom.json").exists(),
            "provenance": Path("out/provenance.json").exists(),
            "cosign_verify": cosign_v or None,
        },
    }

    gates = {"AFV": AFV, "ASE": ASE, "ATC": ATC, "version": "1.0.0"}

    out.write_text(json.dumps(gates, indent=2), encoding="utf-8")

    print(f"[truth-gates] wrote {out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())


# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
