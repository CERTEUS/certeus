<#
+=====================================================================+
|                              CERTEUS                                |
+=====================================================================+
| FILE:   scripts/check_drat.ps1                                      |
| ROLE:   DRAT checker (Windows, local use)                           |
| DATE:   2025-08-17                                                  |
+=====================================================================+
PL: Stub weryfikujący istnienie pliku DRAT i wyliczający jego SHA256.
EN: Stub that checks DRAT file existence and prints its SHA256.
#>

param(
  [Parameter(Mandatory=$true)][string]$Dir,
  [string]$File = "z3.drat",
  [switch]$Quiet
)

$ErrorActionPreference = "Stop"

function Write-Info($msg){ if(-not $Quiet){ Write-Host "[INFO] $msg" -ForegroundColor Cyan } }
function Write-Ok($msg){ if(-not $Quiet){ Write-Host "[OK]   $msg" -ForegroundColor Green } }
function Write-Err($msg){ Write-Host "[ERR]  $msg" -ForegroundColor Red }

if(-not (Test-Path -Path $Dir -PathType Container)){
  Write-Err "Directory does not exist: $Dir"
  exit 2
}

$target = Join-Path $Dir $File
Write-Info "Checking DRAT at: $target"

if(Test-Path -Path $target -PathType Leaf){
  $hash = (Get-FileHash -Algorithm SHA256 -Path $target).Hash.ToLower()
  Write-Ok "DRAT exists: $target"
  if(-not $Quiet){ Write-Host "sha256:$hash" }
  exit 0
}else{
  Write-Err "DRAT file not found: $target"
  exit 2
}
