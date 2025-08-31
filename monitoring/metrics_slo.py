from __future__ import annotations

from prometheus_client import Counter, Gauge, Histogram

# Gauges for model calibration and decision quality
certeus_ece = Gauge("certeus_ece", "Expected Calibration Error")
certeus_brier = Gauge("certeus_brier", "Brier score")
certeus_abstain_rate = Gauge("certeus_abstain_rate", "Abstain rate")

# Histogram for compile/verification durations (ms)
certeus_compile_duration_ms = Histogram(
    "certeus_compile_duration_ms",
    "Proof compile/verification duration (ms)",
    buckets=(5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000),
)

# Counters
certeus_proof_verification_failed_total = Counter(
    "certeus_proof_verification_failed_total", "Proof verification failures"
)
certeus_source_fetch_errors_total = Counter("certeus_source_fetch_errors_total", "Source retrieval/digest errors")

# Gauge for missing digests (alias for SLO Gate input). Kept at 0 unless
# validation flows explicitly set it.
certeus_sources_digest_missing = Gauge("certeus_sources_digest_missing", "Count of sources missing required digests")
