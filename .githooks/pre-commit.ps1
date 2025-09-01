param()
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: .githooks/pre-commit.ps1                            |
# | ROLE: PowerShell script.                                     |
# | PLIK: .githooks/pre-commit.ps1                            |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+
$staged = git diff --name-only --cached
$blocked = @(".env", ".env.local") + ($staged | Where-Object { $_ -like ".devkeys/*" -or $_ -like ".devkeys\*" })
if ($blocked.Count -gt 0) {
  Write-Error "Zablokowano commit tajnych plików: $($blocked -join ', ')"
  exit 1
}

