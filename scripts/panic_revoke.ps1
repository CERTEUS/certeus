#!/usr/bin/env pwsh
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/panic_revoke.ps1                              |
# | ROLE: Panic revoke helper (PowerShell)                      |
# | PLIK: scripts/panic_revoke.ps1                              |
# | ROLA: Skrypt odcięcia i rotacji sekretów                    |
# +-------------------------------------------------------------+

Write-Host "[panic] Revoking tokens and disabling integrations"
Write-Host "- Revoke GitHub App and FGPAT in Settings"
Write-Host "- Rotate GH_RUNNER_TOKEN for self-hosted runners"
Write-Host "- Remove credentials from .git-credentials and runners"
