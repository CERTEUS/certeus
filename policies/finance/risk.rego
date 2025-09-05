package finance.risk

# Policy: deny when risk exceeds threshold

default allow = true

threshold := input.threshold # e.g., {"risk_max": 0.9}

allow {
  not high_risk
}

high_risk {
  rm := input.measure.operators.R
  rm > threshold.risk_max
}

