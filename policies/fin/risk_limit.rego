# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: policies/fin/risk_limit.rego                         |
# | ROLE: OPA policy module.                                     |
# | PLIK: policies/fin/risk_limit.rego                         |
# | ROLA: Moduł polityki OPA.                                    |
# +-------------------------------------------------------------+

package fin.risk

# Deny if aggregated risk exceeds hard limit.
# input: {"signals": {"risk": <0..1>, ...}}

deny[msg] {
  some r
  r := input.signals.risk
  r > 0.7
  msg := sprintf("risk too high: %v", [r])
}
