# CERTEUS — Simple API smoke test (PowerShell)
#
# Starts the dev server, probes key endpoints, then stops the server.
#
# Usage:
#   pwsh -File .\scripts\smoke_api.ps1

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

# Load dev env (keys, CORS, etc.) if present
if (Test-Path .\scripts\dev_env.ps1) { . .\scripts\dev_env.ps1 }

function Start-Server {
  $py = (Resolve-Path .\.venv\Scripts\python.exe).Path
  if (-not (Test-Path $py)) { throw 'Python venv not found: .\\.venv\\Scripts\\python.exe' }
  $args = @('-m','uvicorn','services.api_gateway.main:app','--host','127.0.0.1','--port','8000')
  $proc = Start-Process -FilePath $py -ArgumentList $args -PassThru -WindowStyle Hidden
  for ($i=0; $i -lt 80; $i++) {
    try { $r = Invoke-WebRequest -UseBasicParsing -Uri 'http://127.0.0.1:8000/health' -TimeoutSec 2; if ($r.StatusCode -eq 200) { break } } catch { Start-Sleep -Milliseconds 250 }
  }
  return $proc
}

function Stop-Server([System.Diagnostics.Process]$proc) {
  if ($proc -and -not $proc.HasExited) { Stop-Process -Id $proc.Id -Force }
}

function Hit($method, $path, $bodyJson) {
  $url = 'http://127.0.0.1:8000' + $path
  try {
    if ($method -eq 'GET') {
      $res = Invoke-WebRequest -UseBasicParsing -Uri $url -TimeoutSec 8
    } else {
      $res = Invoke-WebRequest -UseBasicParsing -Method Post -Uri $url -TimeoutSec 8 -ContentType 'application/json' -Body $bodyJson
    }
    $snippet = if ($res.Content.Length -gt 200) { $res.Content.Substring(0,200) + '...' } else { $res.Content }
    "[$method] $path => $($res.StatusCode) len=$($res.Content.Length) body=$snippet"
  } catch {
    "[$method] $path => ERROR: $($_.Exception.Message)"
  }
}

$proc = $null
try {
  $proc = Start-Server
  Hit 'GET' '/health' $null | Write-Host
  Hit 'GET' '/' $null | Write-Host
  Hit 'GET' '/metrics' $null | Write-Host
  Hit 'GET' '/.well-known/jwks.json' $null | Write-Host
  Hit 'GET' '/v1/packs/' $null | Write-Host
  Hit 'POST' '/v1/fin/alpha/measure' '{"signals":{"risk":0.10,"sentiment":0.55}}' | Write-Host
  Hit 'GET' '/v1/fin/alpha/uncertainty' $null | Write-Host
  Hit 'GET' '/v1/fin/alpha/entanglements' $null | Write-Host
} finally {
  Stop-Server $proc
}

