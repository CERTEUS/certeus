# CERTEUS — Simple API smoke test (PowerShell)
#
# Starts the dev server, probes key endpoints, then stops the server.
#
# Usage:
#   pwsh -File .\scripts\smoke_api.ps1

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

# Load dev env (CORS/JWKS), keys and .env if present
if (Test-Path .\scripts\dev_env.ps1) { . .\scripts\dev_env.ps1 }
if (Test-Path .\scripts\keys_dev.ps1) { pwsh -File .\scripts\keys_dev.ps1 | Out-Host }
if (Test-Path .\scripts\env_load.ps1) { . .\scripts\env_load.ps1 }

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

  # CFE
  Hit 'POST' '/v1/cfe/geodesic' '{"case":"CER-SMOKE","facts":{},"norms":{}}' | Write-Host
  Hit 'POST' '/v1/cfe/horizon' '{}' | Write-Host
  Hit 'GET' '/v1/cfe/lensing' $null | Write-Host

  # QTMP
  Hit 'POST' '/v1/qtm/init_case' '{"basis":["ALLOW","DENY","ABSTAIN"]}' | Write-Host
  Hit 'POST' '/v1/qtm/measure' '{"operator":"W","source":"ui"}' | Write-Host
  Hit 'POST' '/v1/qtm/commutator' '{"A":"X","B":"Y"}' | Write-Host
  Hit 'POST' '/v1/qtm/find_entanglement' '{"variables":["A","B"]}' | Write-Host

  # Devices
  Hit 'POST' '/v1/devices/horizon_drive/plan' '{}' | Write-Host
  Hit 'POST' '/v1/devices/qoracle/expectation' '{"objective":"maximize fairness","constraints":{}}' | Write-Host
  Hit 'POST' '/v1/devices/entangle' '{"variables":["RISK","SENTIMENT"],"target_negativity":0.1}' | Write-Host
  Hit 'POST' '/v1/devices/chronosync/reconcile' '{"coords":{"t":0},"pc_delta":{}}' | Write-Host

  # Ethics
  Hit 'POST' '/v1/ethics/equity_meter' '{"distribution_a":[0.2,0.8],"distribution_b":[0.5,0.5]}' | Write-Host
  Hit 'POST' '/v1/ethics/double_verdict' '{"W_litera":"ALLOW","T_telos":"TRUTH","rationale":"smoke"}' | Write-Host

  # DR
  Hit 'POST' '/v1/dr/replay' '{"case":"CER-1","timestamp":"2023-10-01T00:00:00Z"}' | Write-Host
  Hit 'POST' '/v1/dr/recall' '{"upn":"UPN-TEST"}' | Write-Host

  # Export
  Hit 'POST' '/v1/export' '{"case_id":"CER-1","analysis_result":{"ok":true}}' | Write-Host

  # ChatOps
  Hit 'POST' '/v1/chatops/command' '{"cmd":"cfe.geodesic","args":{}}' | Write-Host

  # Ledger
  $rand = -join ((65..70 + 48..57) | Get-Random -Count 64 | ForEach-Object {[char]$_})
  Hit 'POST' '/v1/ledger/record-input' ("{`"case_id`":`"CER-1`",`"document_hash`":`"sha256:" + $rand + "`"}") | Write-Host
  Hit 'GET' '/v1/ledger/CER-1/records' $null | Write-Host
  Hit 'GET' '/v1/ledger/CER-1/prove' $null | Write-Host

  # FHIR connector
  Hit 'POST' '/v1/connectors/fhir/reason' '{"reason":"test"}' | Write-Host

  # Verify (Truth Engine)
  $smt = "(set-logic QF_UF) (declare-fun x () Bool) (assert x) (check-sat)"
  Hit 'POST' '/v1/verify' ("{`"formula`":`"$smt`",`"lang`":`"smt2`"}") | Write-Host

  # PCO bundle + public verify
  $rid = 'RID-SMOKE-1'
  $payload = '{"rid":"' + $rid + '","smt2_hash":"' + ('0'*64) + '","lfsc":"(lfsc proof)","drat":"p drat","merkle_proof":[]}'
  Hit 'POST' '/v1/pco/bundle' $payload | Write-Host
  Hit 'GET' ('/pco/public/' + $rid) $null | Write-Host

  # Preview upload (multipart via curl.exe)
  $tmpTxt = Join-Path $env:TEMP ('preview_' + [guid]::NewGuid().ToString('N') + '.txt')
  'hello world' | Set-Content -LiteralPath $tmpTxt -Encoding UTF8
  try {
    $code = & curl.exe -s -o NUL -w "%{http_code}" -F ("file=@" + $tmpTxt + ";type=text/plain") http://127.0.0.1:8000/v1/preview
    Write-Host "[POST] /v1/preview => $code"
  } catch { Write-Host "[POST] /v1/preview => ERROR: $($_.Exception.Message)" }

  # System ingest/analyze (multipart PDF + query)
  $tmpPdf = Join-Path $env:TEMP ('doc_' + [guid]::NewGuid().ToString('N') + '.pdf')
  '%PDF-1.4`n% Smoke`n1 0 obj<</Type/Catalog>>endobj`ntrailer<<>>`n%%EOF' | Set-Content -LiteralPath $tmpPdf -Encoding ASCII
  try {
    $code = & curl.exe -s -o NUL -w "%{http_code}" -F ("file=@" + $tmpPdf + ";type=application/pdf") http://127.0.0.1:8000/v1/ingest
    Write-Host "[POST] /v1/ingest => $code"
  } catch { Write-Host "[POST] /v1/ingest => ERROR: $($_.Exception.Message)" }
  try {
    $code = & curl.exe -s -o NUL -w "%{http_code}" -F ("file=@" + $tmpPdf + ";type=application/pdf") "http://127.0.0.1:8000/v1/analyze?case_id=CER-1"
    Write-Host "[POST] /v1/analyze => $code"
  } catch { Write-Host "[POST] /v1/analyze => ERROR: $($_.Exception.Message)" }

  # Source cache (file://)
  $tmpSrc = Join-Path $env:TEMP ('src_' + [guid]::NewGuid().ToString('N') + '.txt')
  'source-cache' | Set-Content -LiteralPath $tmpSrc -Encoding UTF8
  Hit 'POST' '/v1/sources/cache' ("{`"uri`":`"file:///$($tmpSrc -replace '\\','/')`"}") | Write-Host

  # Publish (not mounted in app: /defx/reason) — skipped
} finally {
  Stop-Server $proc
}
