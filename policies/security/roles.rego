# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: policies/security/roles.rego                         |
# | ROLE: OPA policy module (roles, fine-grained access)        |
# | PLIK: policies/security/roles.rego                         |
# | ROLA: Moduł polityki OPA (role, fine-grained access)        |
# +-------------------------------------------------------------+

package security.roles

# Skeleton policy for role-based decisions (W9 scaffolding).
# Input example:
# {
#   "user": {"id": "u1", "role": "AFV"},
#   "action": "publish",       # read | publish | merge | approve | revoke | manage_policy | manage_keys
#   "resource": {"kind": "pco", "case_id": "CER-LEX-99", "scope": "legal"}
# }

default allow = false

# Known governance roles
roles := {"AFV", "ASE", "ATC", "ATS", "AVR"}

# Supported actions
actions := {"read", "publish", "merge", "approve", "revoke", "manage_policy", "manage_keys"}

# Resource kinds (generic; refine per governance pack)
rkinds := {"pco", "policy", "keys", "config"}

# Basic input guards
valid_input {
  roles[input.user.role]
  actions[input.action]
  rkinds[input.resource.kind]
}

# READ: any known role
allow {
  valid_input
  input.action == "read"
}

# PUBLISH: AFV, ATC (auditor/verifier or change control). Approval flow handled upstream.
allow {
  valid_input
  input.action == "publish"
  {"AFV", "ATC"}[input.user.role]
}

# APPROVE: AFV, AVR (review).
allow {
  valid_input
  input.action == "approve"
  {"AFV", "AVR"}[input.user.role]
}

# REVOKE: ATC only (change control / revocation authority).
allow {
  valid_input
  input.action == "revoke"
  input.user.role == "ATC"
}

# MERGE (policy/config): ATC, ASE.
allow {
  valid_input
  input.action == "merge"
  {"ATC", "ASE"}[input.user.role]
  {"policy", "config"}[input.resource.kind]
}

# MANAGE_POLICY: ASE only.
allow {
  valid_input
  input.action == "manage_policy"
  input.user.role == "ASE"
}

# MANAGE_KEYS: ASE only (key management guardianship).
allow {
  valid_input
  input.action == "manage_keys"
  input.user.role == "ASE"
  input.resource.kind == "keys"
}

# Deny messages for auditability
deny[msg] {
  not allow
  msg := sprintf("role %v not permitted for %v on %v", [input.user.role, input.action, input.resource.kind])
}
