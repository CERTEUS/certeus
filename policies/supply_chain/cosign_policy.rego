package sigpolicy

# Simple policy for cosign verify-attestation --policy
# Allows only in-toto statements with SLSA provenance predicate

default allow = false

allow {
  input._type == "https://in-toto.io/Statement/v1"
  valid_predicate
}

valid_predicate {
  input.predicateType == "https://slsa.dev/provenance/v1"
}

valid_predicate {
  input.predicateType == "https://slsa.dev/provenance/v0.2"
}

