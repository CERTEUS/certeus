package security.dp

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: policies/security/dp.rego                            |
# | ROLE: OPA Policy — Data Protection (DP)                     |
# +-------------------------------------------------------------+

default allow = false

# Context keys:
# - input.context.redacted: boolean (true if boundary redaction applied)
# - input.context.purpose: string (billing|research_anonymized|ops|other)

# PII fields (example list). In production extend via data.security.pii
pii_keys = {"ssn", "email", "phone", "pesel", "dob"}

has_pii {
  some k
  input.payload[k]
  k_lc := lower(k)
  pii_keys[k_lc]
}

allow {
  not has_pii
}

allow {
  has_pii
  input.context.redacted == true
}

allow {
  has_pii
  input.context.purpose == "research_anonymized"
}

deny_reason[reason] {
  not allow
  reason := "pii_present_without_redaction"
}

