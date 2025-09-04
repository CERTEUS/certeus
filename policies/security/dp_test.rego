package security

# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: policies/security/dp_test.rego                       |
# | ROLE: OPA Tests — Data Protection (DP)                       |
# +-------------------------------------------------------------+

import data.security.dp

test_allow_without_pii {
  input := {"payload": {"msg": "hello"}, "context": {"redacted": false}}
  dp.allow with input as input
}

test_deny_with_pii_no_redaction {
  input := {"payload": {"email": "a@b"}, "context": {"redacted": false}}
  not dp.allow with input as input
}

test_allow_with_redaction {
  input := {"payload": {"email": "a@b"}, "context": {"redacted": true}}
  dp.allow with input as input
}

test_allow_for_research_purpose {
  input := {"payload": {"pesel": "123"}, "context": {"redacted": false, "purpose": "research_anonymized"}}
  dp.allow with input as input
}

