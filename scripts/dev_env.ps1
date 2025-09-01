# CERTEUS — Developer environment bootstrap (PowerShell)
#
# Usage:
#   . .\scripts\dev_env.ps1    # dot-source to set env in current session
#   $env:ED25519_PUBKEY_HEX     # should be set (32 bytes, hex)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Set-IfEmpty {
  param(
    [Parameter(Mandatory=$true)][string]$Name,
    [Parameter(Mandatory=$true)][string]$Value
  )
  if (-not $env:$Name) { $env:$Name = $Value }
}

# Allow all origins in dev (adjust as needed)
Set-IfEmpty -Name 'ALLOW_ORIGINS' -Value '*'

# JWKS public key for /.well-known/jwks.json
# If not provided, set to 32 bytes of zeros (dev-safe placeholder)
if (-not $env:ED25519_PUBKEY_B64URL -and -not $env:ED25519_PUBKEY_HEX) {
  $env:ED25519_PUBKEY_HEX = ('00' * 32)
}

Write-Host 'DEV ENV:'
Write-Host '  ALLOW_ORIGINS=' $env:ALLOW_ORIGINS
Write-Host '  ED25519_PUBKEY_B64URL set? ' ([bool]$env:ED25519_PUBKEY_B64URL)
Write-Host '  ED25519_PUBKEY_HEX    set? ' ([bool]$env:ED25519_PUBKEY_HEX)

