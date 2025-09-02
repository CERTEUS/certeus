# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: policies/security/roles.rego                         |
# | ROLE: OPA policy module (roles, fine-grained access)        |
# | PLIK: policies/security/roles.rego                         |
# | ROLA: Moduł polityki OPA (role, fine-grained access)        |
# +-------------------------------------------------------------+

package security.roles

# Skeleton policy for role-based decisions.
# Input example:
# {
#   "user": {"id": "u1", "role": "AFV"},
#   "action": "publish",
#   "resource": {"kind": "pco", "case_id": "CER-LEX-99"}
# }

default allow = false

roles := {"AFV", "ASE", "ATC", "ATS", "AVR"}

# Allow safe read for all known roles
allow {
  roles[input.user.role]
  input.action == "read"
}

# Publish requires counsel/AFV/ATC signatures upstream
allow {
  roles[input.user.role]
  input.action == "publish"
}

# Merge (e.g., policy/config) allowed to ATC/ASE
allow {
  {"ATC", "ASE"}[input.user.role]
  input.action == "merge"
}

# Deny messages for auditability
deny[msg] {
  not allow
  msg := sprintf("role %v not permitted for %v", [input.user.role, input.action])
}

