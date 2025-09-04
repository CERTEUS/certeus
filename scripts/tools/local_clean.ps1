#!/usr/bin/env pwsh
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/tools/local_clean.ps1                        |
# | ROLE: Safe local cleanup of ignored files                   |
# | PLIK: scripts/tools/local_clean.ps1                        |
# | ROLA: Bezpieczne czyszczenie plików ignorowanych            |
# +-------------------------------------------------------------+

<#
PL: Czyści lokalne artefakty i pliki ignorowane przez git (git clean -fdX)
    bez naruszania śledzonych zmian. Domyślnie wyświetla podgląd i pyta
    o potwierdzenie.

EN: Cleans local artifacts and git-ignored files (git clean -fdX) without
    touching tracked changes. Shows a preview and asks for confirmation
    by default.
#>

param(
  [switch]$Yes
)

$ErrorActionPreference = 'Stop'

function Assert-GitRepo {
  $top = git rev-parse --show-toplevel 2>$null
  if (-not $top) { throw 'Not inside a git repository.' }
  return $top
}

function Show-Preview {
  Write-Host 'Preview (git clean -nXdf):' -ForegroundColor Cyan
  git clean -nXdf | ForEach-Object { Write-Host "  $_" }
}

try {
  $repo = Assert-GitRepo
  Push-Location $repo
  Show-Preview
  if (-not $Yes) {
    $ans = Read-Host 'Proceed with cleanup? (y/N)'
    if ($ans -notin @('y','Y','yes','YES')) { Write-Host 'Aborted.'; exit 0 }
  }
  git clean -Xdf
  Write-Host 'Cleanup completed.' -ForegroundColor Green
} finally {
  Pop-Location 2>$null
}

