# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/demos/w1_demo.ps1                           |
# | ROLE: PowerShell script (W1 demo).                          |
# | PLIK: scripts/demos/w1_demo.ps1                           |
# | ROLA: Skrypt PowerShell (demo W1).                          |
# +-------------------------------------------------------------+

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

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
    if ($method -eq 'GET') { $res = Invoke-WebRequest -UseBasicParsing -Uri $url -TimeoutSec 8 }
    else { $res = Invoke-WebRequest -UseBasicParsing -Method Post -Uri $url -TimeoutSec 8 -ContentType 'application/json' -Body $bodyJson }
    $json = $null
    try { $json = $res.Content | ConvertFrom-Json -ErrorAction Stop } catch {}
    [pscustomobject]@{ method=$method; path=$path; code=[int]$res.StatusCode; ok=([int]$res.StatusCode -ge 200 -and [int]$res.StatusCode -lt 300); json=$json }
  } catch {
    [pscustomobject]@{ method=$method; path=$path; code=0; ok=$false; json=$null }
  }
}

$items = @()
$proc = $null
try {
  $proc = Start-Server
  # ChatOps (cfe.geodesic)
  $items += Hit 'POST' '/v1/chatops/command' '{"cmd":"cfe.geodesic","args":{}}'
  # MailOps ingest
  $mail = '{"mail_id":"DEMO-W1-EMAIL","from_addr":"demo@example.com","to":["ops@example.com"],"subject":"Demo","body_text":"W1 demo","spf":"pass","dkim":"pass","dmarc":"pass","attachments":[]}'
  $items += Hit 'POST' '/v1/mailops/ingest' $mail
  # QTMP measure + history
  $items += Hit 'POST' '/v1/qtm/measure' '{"operator":"L","source":"demo","case":"DEMO-W1"}'
  $items += Hit 'GET' '/v1/qtm/history/DEMO-W1' $null
  # Telemetry: CFE/lexqft
  $items += Hit 'GET' '/v1/cfe/curvature' $null
  $items += Hit 'GET' '/v1/lexqft/coverage' $null
  # Ledger check (empty by default but endpoint alive)
  $items += Hit 'GET' '/v1/ledger/DEMO-W1/records' $null
} finally {
  try { New-Item -ItemType Directory -Force -Path reports | Out-Null } catch {}
  $out = $items | ConvertTo-Json -Depth 6
  Set-Content -LiteralPath 'reports/w1_demo.json' -Value $out -Encoding UTF8
  Stop-Server $proc
}

Write-Host "W1 Demo summary saved to reports/w1_demo.json"
