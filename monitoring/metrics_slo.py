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

from collections import deque
from threading import Lock

from prometheus_client import Counter, Gauge, Histogram

# In‑proc lightweight aggregator for quick summaries (landing widgets, API)
_REQ_AGG_LOCK: Lock = Lock()
_REQ_AGG: dict[tuple[str, str], dict[str, float]] = {}
_SERIES: dict[tuple[str, str], deque[float]] = {}


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
        dq = _SERIES.get(key)
        if dq is None:
            dq = deque(maxlen=200)
            _SERIES[key] = dq
        dq.append(float(dur_ms))


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


def http_series(top: int = 5) -> dict[str, object]:
    """Return series for top endpoints by count with p95 and last durations.

    The series contains up to 200 most recent durations (ms) per path/method.
    """

    with _REQ_AGG_LOCK:
        counts = [(k, int(v.get("count", 0.0))) for k, v in _REQ_AGG.items()]
        top_keys = [k for (k, _) in sorted(counts, key=lambda x: x[1], reverse=True)[:top]]
        out = []
        for k in top_keys:
            pts = list(_SERIES.get(k, deque()))
            if pts:
                s = sorted(pts)
                # p95 index
                idx = int(0.95 * (len(s) - 1))
                p95 = s[idx]
            else:
                p95 = 0.0
            out.append({"path": k[0], "method": k[1], "points": pts, "p95": p95, "count": len(pts)})
    return {"series": out}


# Gauges for model calibration and decision quality

certeus_ece = Gauge("certeus_ece", "Expected Calibration Error")

certeus_brier = Gauge("certeus_brier", "Brier score")

certeus_abstain_rate = Gauge("certeus_abstain_rate", "Abstain rate")

# CFE: Ricci (kappa_max)
certeus_cfe_kappa_max = Gauge("certeus_cfe_kappa_max", "CFE kappa_max curvature")

# CFE: Geodesic action (hist) and Horizon mass (gauge)
certeus_cfe_geodesic_action = Histogram(
    "certeus_cfe_geodesic_action",
    "CFE geodesic action",
    buckets=(1, 2, 3, 5, 8, 13, 21, 34),
)
certeus_cfe_horizon_mass = Gauge("certeus_cfe_horizon_mass", "CFE horizon mass")

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

# HTTP load shedding counter
certeus_http_shed_total = Counter(
    "certeus_http_shed_total",
    "Total HTTP shed events",
    labelnames=("tenant", "path", "method", "reason"),
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

# LexQFT: Coverage (gamma, uncaptured) + energy debt
certeus_lexqft_coverage_gamma = Gauge("certeus_lexqft_coverage_gamma", "LexQFT coverage gamma (aggregated)")
certeus_lexqft_uncaptured_mass = Gauge("certeus_lexqft_uncaptured_mass", "LexQFT uncaptured mass (aggregated)")
certeus_lexqft_energy_debt = Gauge("certeus_lexqft_energy_debt", "LexQFT energy debt (per case)", labelnames=("case",))

# FINENITH: entanglement MI and commutator
certeus_fin_entanglement_mi = Gauge(
    "certeus_fin_entanglement_mi", "FIN entanglement mutual information", labelnames=("a", "b")
)
certeus_fin_commutator_rs = Gauge("certeus_fin_commutator_rs", "FIN commutator [R,S] norm (non-commuting -> >0)")

# FINENITH: paper trading (W5)
certeus_fin_paper_orders_total = Counter(
    "certeus_fin_paper_orders_total",
    "FIN paper trading orders total",
    labelnames=("tenant", "side"),
)
certeus_fin_paper_equity = Gauge(
    "certeus_fin_paper_equity",
    "FIN paper trading account equity",
    labelnames=("tenant",),
)

# P2P queue (W8)
certeus_p2p_enqueued_total = Counter(
    "certeus_p2p_enqueued_total",
    "P2P enqueued jobs",
    labelnames=("device",),
)
certeus_p2p_dequeued_total = Counter(
    "certeus_p2p_dequeued_total",
    "P2P dequeued jobs",
    labelnames=("device",),
)
certeus_p2p_queue_depth = Gauge("certeus_p2p_queue_depth", "P2P queue depth")

# Devices signatures (W9)
certeus_devices_signed_total = Counter(
    "certeus_devices_signed_total",
    "Device outputs signed",
    labelnames=("device",),
)

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

# LEX Micro‑Court (W6)
certeus_lex_micro_court_locked_total = Counter(
    "certeus_lex_micro_court_locked_total",
    "LEX Micro‑Court locked events",
    labelnames=("case", "tenant"),
)
certeus_lex_micro_court_published_total = Counter(
    "certeus_lex_micro_court_published_total",
    "LEX Micro‑Court published events",
    labelnames=("case", "tenant"),
)
