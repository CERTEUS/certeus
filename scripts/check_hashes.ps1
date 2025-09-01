# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/check_hashes.ps1                            |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/check_hashes.ps1                            |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# +======================================================================+
# |                               CERTEUS                                |
# +======================================================================+
# | FILE / PLIK: scripts/check_hashes.ps1                                |
# | ROLA / ROLE:                                                          |
# |  PL: Oblicza SHA256 plików DRAT/LFSC w proof_artifacts.               |
# |  EN: Compute SHA256 for DRAT/LFSC files in proof_artifacts.           |
# +======================================================================+
Param(
    [string]$Dir = "proof_artifacts"
)
$drat = Join-Path $Dir "z3.drat"
$lfsc = Join-Path $Dir "cvc5.lfsc"
if (Test-Path $drat) { Get-FileHash $drat -Algorithm SHA256 }
if (Test-Path $lfsc) { Get-FileHash $lfsc -Algorithm SHA256 }
