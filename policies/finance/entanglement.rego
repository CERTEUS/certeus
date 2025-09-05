package finance.entanglement

# Policy: require MI below max for publish (prevent over‑entanglement)

default allow = true

threshold := input.threshold # e.g., {"mi_max": 0.75}

allow {
  not too_entangled
}

too_entangled {
  some i
  mi := input.mi[i]
  mi.value > threshold.mi_max
}

