"""

PL: Moduł CERTEUS – uzupełnij opis funkcjonalny.

EN: CERTEUS module – please complete the functional description.

"""

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

# === MODELE / MODELS ===

# === LOGIKA / LOGIC ===

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===

# +-------------------------------------------------------------+

# |                          CERTEUS                            |

# +-------------------------------------------------------------+

# | FILE: monitoring/metrics_slo.py                           |

# | ROLE: Project module.                                       |

# | PLIK: monitoring/metrics_slo.py                           |

# | ROLA: Moduł projektu.                                       |

# +-------------------------------------------------------------+

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

# Decision counters (ProofGate)

certeus_publish_total = Counter("certeus_publish_total", "Number of PUBLISH decisions")

certeus_conditional_total = Counter("certeus_conditional_total", "Number of CONDITIONAL decisions")

certeus_pending_total = Counter("certeus_pending_total", "Number of PENDING decisions")

certeus_abstain_total = Counter("certeus_abstain_total", "Number of ABSTAIN decisions")


def observe_decision(decision: str) -> None:
    """Increment counters and update abstain_rate gauge (lifetime ratio)."""

    if decision == "PUBLISH":
        certeus_publish_total.inc()

    elif decision == "CONDITIONAL":
        certeus_conditional_total.inc()

    elif decision == "PENDING":
        certeus_pending_total.inc()

    elif decision == "ABSTAIN":
        certeus_abstain_total.inc()

    # Update abstain rate as ratio of abstain to total

    try:
        total = (
            certeus_publish_total._value.get()  # type: ignore[attr-defined]
            + certeus_conditional_total._value.get()  # type: ignore[attr-defined]
            + certeus_pending_total._value.get()  # type: ignore[attr-defined]
            + certeus_abstain_total._value.get()  # type: ignore[attr-defined]
        )

        abstain = certeus_abstain_total._value.get()  # type: ignore[attr-defined]

        if total > 0:
            certeus_abstain_rate.set(abstain / total)

    except Exception:
        pass


# HTTP request duration (Gateway)

certeus_http_request_duration_ms = Histogram(
    "certeus_http_request_duration_ms",
    "Gateway HTTP request duration (ms)",
    labelnames=("path", "method", "status"),
    buckets=(5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000),
)

# QTMP: Uncertainty bound and operator priorities
certeus_qtm_ub_lt = Gauge("certeus_qtm_ub_lt", "QTMP uncertainty bound L_T", labelnames=("source",))
certeus_qtm_operator_priority = Gauge(
    "certeus_qtm_operator_priority",
    "QTMP operator priority",
    labelnames=("operator",),
)

# LexQFT: Coverage (gamma, uncaptured)
certeus_lexqft_coverage_gamma = Gauge("certeus_lexqft_coverage_gamma", "LexQFT coverage gamma (aggregated)")
certeus_lexqft_uncaptured_mass = Gauge("certeus_lexqft_uncaptured_mass", "LexQFT uncaptured mass (aggregated)")

# FINENITH: entanglement MI and commutator
certeus_fin_entanglement_mi = Gauge(
    "certeus_fin_entanglement_mi", "FIN entanglement mutual information", labelnames=("a", "b")
)
certeus_fin_commutator_rs = Gauge("certeus_fin_commutator_rs", "FIN commutator [R,S] norm (non-commuting -> >0)")
