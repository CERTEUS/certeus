# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: policies/fin/signals_dp.rego                        |
# | ROLE: OPA policy module.                                     |
# | PLIK: policies/fin/signals_dp.rego                        |
# | ROLA: Moduł polityki OPA.                                    |
# +-------------------------------------------------------------+

package fin.dp

# Require dp_epsilon to be present and <= 1.0

deny[msg] {
  not input.dp_epsilon
  msg := "missing dp_epsilon"
}

deny[msg] {
  e := input.dp_epsilon
  e > 1.0
  msg := sprintf("dp_epsilon too high: %v", [e])
}
