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
from threading import Lock

# In‑proc lightweight aggregator for quick summaries (landing widgets, API)
_REQ_AGG_LOCK: Lock = Lock()
_REQ_AGG: dict[tuple[str, str], dict[str, float]] = {}


def record_http_observation(path: str, method: str, status: str, tenant: str, dur_ms: float) -> None:
    """Record a simple aggregate for (path, method): count, sum_ms, last_ms.

    This is supplementary to Prometheus metrics and intended for quick JSON
    summaries without scraping the /metrics exposition.
    """

    key = (str(path), str(method))
    with _REQ_AGG_LOCK:
        st = _REQ_AGG.get(key)
        if not st:
            st = {"count": 0.0, "sum_ms": 0.0, "last_ms": 0.0}
            _REQ_AGG[key] = st
        st["count"] += 1.0
        st["sum_ms"] += float(dur_ms)
        st["last_ms"] = float(dur_ms)


def http_summary(top: int = 10) -> dict[str, object]:
    """Return a snapshot summary of top endpoints by average latency and by count."""

    with _REQ_AGG_LOCK:
        items = [
            {
                "path": k[0],
                "method": k[1],
                "count": int(v.get("count", 0.0)),
                "avg_ms": (v.get("sum_ms", 0.0) / v.get("count", 1.0)),
                "last_ms": v.get("last_ms", 0.0),
            }
            for k, v in _REQ_AGG.items()
        ]
    by_avg = sorted(items, key=lambda x: x["avg_ms"], reverse=True)[:top]
    by_count = sorted(items, key=lambda x: x["count"], reverse=True)[:top]
    return {"top_avg_ms": by_avg, "top_count": by_count, "total_paths": len(items)}

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

# Per-tenant HTTP metrics (W16: SLO per tenant)
certeus_http_request_duration_ms_tenant = Histogram(
    "certeus_http_request_duration_ms_tenant",
    "Gateway HTTP request duration (ms) per tenant",
    labelnames=("tenant", "path", "method", "status"),
    buckets=(5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000),
)
certeus_http_requests_total = Counter(
    "certeus_http_requests_total",
    "Total HTTP requests by tenant/path/method/status",
    labelnames=("tenant", "path", "method", "status"),
)

# QTMP: Uncertainty bound and operator priorities
certeus_qtm_ub_lt = Gauge("certeus_qtm_ub_lt", "QTMP uncertainty bound L_T", labelnames=("source",))
certeus_qtm_operator_priority = Gauge(
    "certeus_qtm_operator_priority",
    "QTMP operator priority",
    labelnames=("operator",),
)

# QTMP: Collapses, expectation values, history length
certeus_qtm_collapse_total = Counter(
    "certeus_qtm_collapse_total",
    "QTMP collapses total",
    labelnames=("operator", "verdict"),
)
certeus_qtm_expectation_value = Gauge(
    "certeus_qtm_expectation_value",
    "QTMP expectation value",
    labelnames=("case", "operator"),
)
certeus_qtm_history_len = Gauge(
    "certeus_qtm_history_len",
    "QTMP history length",
    labelnames=("case",),
)

# QTMP: Collapse probability histogram and CFE-QTMP correlation
certeus_qtm_collapse_prob = Histogram(
    "certeus_qtm_collapse_prob",
    "QTMP collapse probability",
    labelnames=("operator",),
    buckets=(0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0),
)
certeus_qtm_cfe_correlation = Gauge(
    "certeus_qtm_cfe_correlation",
    "CFE-QTMP correlation",
    labelnames=("case",),
)

# LexQFT: Coverage (gamma, uncaptured)
certeus_lexqft_coverage_gamma = Gauge("certeus_lexqft_coverage_gamma", "LexQFT coverage gamma (aggregated)")
certeus_lexqft_uncaptured_mass = Gauge("certeus_lexqft_uncaptured_mass", "LexQFT uncaptured mass (aggregated)")

# FINENITH: entanglement MI and commutator
certeus_fin_entanglement_mi = Gauge(
    "certeus_fin_entanglement_mi", "FIN entanglement mutual information", labelnames=("a", "b")
)
certeus_fin_commutator_rs = Gauge("certeus_fin_commutator_rs", "FIN commutator [R,S] norm (non-commuting -> >0)")

# LEX Pilot (W16): feedback counters and latest rating
certeus_lex_pilot_feedback_total = Counter(
    "certeus_lex_pilot_feedback_total",
    "LEX pilot feedback submissions",
    labelnames=("case", "tenant"),
)
certeus_lex_pilot_last_rating = Gauge(
    "certeus_lex_pilot_last_rating",
    "LEX pilot last feedback rating",
    labelnames=("case", "tenant"),
)
