# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smoke_api.ps1                               |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/smoke_api.ps1                               |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# CERTEUS — Simple API smoke test (PowerShell)
#
# Starts the dev server, probes key endpoints, then stops the server.
#
# Usage:
#   pwsh -File .\scripts\smoke_api.ps1

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

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
  for ($i=0; $i -lt 120; $i++) {
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
    [pscustomobject]@{ method=$method; path=$path; code=[int]$res.StatusCode; ok=([int]$res.StatusCode -ge 200 -and [int]$res.StatusCode -lt 300); msg="len=$($res.Content.Length) body=$snippet" }
  } catch {
    [pscustomobject]@{ method=$method; path=$path; code=0; ok=$false; msg="ERROR: $($_.Exception.Message)" }
  }
}

$results = @()
$proc = $null
try {
  $proc = Start-Server
  $results += Hit 'GET' '/health' $null
  $results += Hit 'GET' '/' $null
  $results += Hit 'GET' '/metrics' $null
  $results += Hit 'GET' '/.well-known/jwks.json' $null
  $results += Hit 'GET' '/v1/packs/' $null

  # CFE
  $results += Hit 'POST' '/v1/cfe/geodesic' '{"case":"CER-SMOKE","facts":{},"norms":{}}'
  $results += Hit 'POST' '/v1/cfe/horizon' '{}'
  $results += Hit 'GET' '/v1/cfe/lensing' $null

  # QTMP
  $results += Hit 'POST' '/v1/qtm/init_case' '{"basis":["ALLOW","DENY","ABSTAIN"]}'
  $results += Hit 'POST' '/v1/qtm/measure' '{"operator":"W","source":"ui"}'
  $results += Hit 'POST' '/v1/qtm/measure' '{"operator":"L","source":"smoke","case":"SMOKE-QTMP-1"}'
  $results += Hit 'GET' '/v1/qtm/history/SMOKE-QTMP-1' $null
  $results += Hit 'POST' '/v1/qtm/commutator' '{"A":"X","B":"Y"}'
  $results += Hit 'POST' '/v1/qtm/find_entanglement' '{"variables":["A","B"]}'

  # Devices
  $results += Hit 'POST' '/v1/devices/horizon_drive/plan' '{}'
  $results += Hit 'POST' '/v1/devices/qoracle/expectation' '{"objective":"maximize fairness","constraints":{}}'
  $results += Hit 'POST' '/v1/devices/entangle' '{"variables":["RISK","SENTIMENT"],"target_negativity":0.1}'
  $results += Hit 'POST' '/v1/devices/chronosync/reconcile' '{"coords":{"t":0},"pc_delta":{}}'

  # Ethics
  $results += Hit 'POST' '/v1/ethics/equity_meter' '{"distribution_a":[0.2,0.8],"distribution_b":[0.5,0.5]}'
  $results += Hit 'POST' '/v1/ethics/double_verdict' '{"W_litera":"ALLOW","T_telos":"TRUTH","rationale":"smoke"}'

  # DR
  $results += Hit 'POST' '/v1/dr/replay' '{"case":"CER-1","timestamp":"2023-10-01T00:00:00Z"}'
  $results += Hit 'POST' '/v1/dr/recall' '{"upn":"UPN-TEST"}'

  # Export
  $results += Hit 'POST' '/v1/export' '{"case_id":"CER-1","analysis_result":{"ok":true}}'

  # ChatOps
  $results += Hit 'POST' '/v1/chatops/command' '{"cmd":"cfe.geodesic","args":{}}'

  # MailOps
  $mail = '{"mail_id":"SMOKE-EMAIL-1","from_addr":"smoke@example.com","to":["ops@example.com"],"subject":"Smoke","body_text":"Hello","spf":"pass","dkim":"pass","dmarc":"pass","attachments":[]}'
  $results += Hit 'POST' '/v1/mailops/ingest' $mail

  # Ledger
  $rand = -join ((65..70 + 48..57) | Get-Random -Count 64 | ForEach-Object {[char]$_})
  $results += Hit 'POST' '/v1/ledger/record-input' ("{`"case_id`":`"CER-1`",`"document_hash`":`"sha256:" + $rand + "`"}")
  $results += Hit 'GET' '/v1/ledger/CER-1/records' $null
  $results += Hit 'GET' '/v1/ledger/CER-1/prove' $null

  # FHIR connector
  $results += Hit 'POST' '/v1/connectors/fhir/reason' '{"reason":"test"}'

  # Verify (Truth Engine)
  $smt = "(set-logic QF_UF) (declare-fun x () Bool) (assert x) (check-sat)"
  $results += Hit 'POST' '/v1/verify' ("{`"formula`":`"$smt`",`"lang`":`"smt2`"}")

  # PCO bundle + public verify
  $rid = 'RID-SMOKE-1'
  $payload = '{"rid":"' + $rid + '","smt2_hash":"' + ('0'*64) + '","lfsc":"(lfsc proof)","drat":"p drat","merkle_proof":[]}'
  $results += Hit 'POST' '/v1/pco/bundle' $payload
  $results += Hit 'GET' ('/pco/public/' + $rid) $null

  # Preview upload (multipart via curl.exe)
  $tmpTxt = Join-Path $env:TEMP ('preview_' + [guid]::NewGuid().ToString('N') + '.txt')
  'hello world' | Set-Content -LiteralPath $tmpTxt -Encoding UTF8
  try {
    $code = & curl.exe -s -o NUL -w "%{http_code}" -F ("file=@" + $tmpTxt + ";type=text/plain") http://127.0.0.1:8000/v1/preview
    $results += [pscustomobject]@{ method='POST'; path='/v1/preview'; code=[int]$code; ok=([int]$code -ge 200 -and [int]$code -lt 300); msg='' }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/preview'; code=0; ok=$false; msg=$_.Exception.Message } }

  # System ingest/analyze (multipart PDF + query)
  $tmpPdf = Join-Path $env:TEMP ('doc_' + [guid]::NewGuid().ToString('N') + '.pdf')
  '%PDF-1.4`n% Smoke`n1 0 obj<</Type/Catalog>>endobj`ntrailer<<>>`n%%EOF' | Set-Content -LiteralPath $tmpPdf -Encoding ASCII
  try {
    $code = & curl.exe -s -o NUL -w "%{http_code}" -F ("file=@" + $tmpPdf + ";type=application/pdf") http://127.0.0.1:8000/v1/ingest
    $results += [pscustomobject]@{ method='POST'; path='/v1/ingest'; code=[int]$code; ok=([int]$code -ge 200 -and [int]$code -lt 300); msg='' }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/ingest'; code=0; ok=$false; msg=$_.Exception.Message } }
  try {
    $code = & curl.exe -s -o NUL -w "%{http_code}" -F ("file=@" + $tmpPdf + ";type=application/pdf") "http://127.0.0.1:8000/v1/analyze?case_id=CER-1"
    $results += [pscustomobject]@{ method='POST'; path='/v1/analyze'; code=[int]$code; ok=([int]$code -ge 200 -and [int]$code -lt 300); msg='' }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/analyze'; code=0; ok=$false; msg=$_.Exception.Message } }

  # Source cache (file://)
  $tmpSrc = Join-Path $env:TEMP ('src_' + [guid]::NewGuid().ToString('N') + '.txt')
  'source-cache' | Set-Content -LiteralPath $tmpSrc -Encoding UTF8
  try {
    $u = 'http://127.0.0.1:8000/v1/sources/cache'
    $body = "{`"uri`":`"file:///$($tmpSrc -replace '\\','/')`"}"
    $r = Invoke-WebRequest -UseBasicParsing -Method Post -Uri $u -TimeoutSec 8 -ContentType 'application/json' -Body $body
    $results += [pscustomobject]@{ method='POST'; path='/v1/sources/cache'; code=[int]$r.StatusCode; ok=($r.StatusCode -eq 200); msg='' }
  } catch {
    try {
      $b64 = [Convert]::ToBase64String([System.Text.Encoding]::UTF8.GetBytes('source-cache'))
      $body2 = "{`"uri`":`"data:text/plain;base64,$b64`"}"
      $r2 = Invoke-WebRequest -UseBasicParsing -Method Post -Uri 'http://127.0.0.1:8000/v1/sources/cache' -TimeoutSec 8 -ContentType 'application/json' -Body $body2
      $results += [pscustomobject]@{ method='POST'; path='/v1/sources/cache#fallback'; code=[int]$r2.StatusCode; ok=($r2.StatusCode -eq 200); msg='data: fallback' }
    } catch {
      $results += [pscustomobject]@{ method='POST'; path='/v1/sources/cache'; code=0; ok=$false; msg=$_.Exception.Message }
    }
  }

  # Publish (not mounted in app: /defx/reason) - skipped

  # --- OpenAPI validation & lightweight schema checks ---
  try {
    New-Item -ItemType Directory -Force -Path reports | Out-Null
    $open = Invoke-WebRequest -UseBasicParsing -Uri 'http://127.0.0.1:8000/openapi.json' -TimeoutSec 8
    if ($open.StatusCode -eq 200) { Set-Content -LiteralPath 'reports\openapi.json' -Value $open.Content -Encoding UTF8 }
    $py = (Resolve-Path .\.venv\Scripts\python.exe).Path
    $code = @'
import json, sys
from pathlib import Path
spec = json.loads(Path('reports/openapi.json').read_text(encoding='utf-8'))
ok = ('openapi' in spec and 'paths' in spec)
try:
    # Try modern API first
    try:
        from openapi_spec_validator import validate_spec as _validate
    except Exception:
        try:
            from openapi_spec_validator.validators import validate as _validate
        except Exception:
            _validate = None
    if _validate is not None:
        _validate(spec)
        ok = True
except Exception as e:
    ok = False
sys.exit(0 if ok else 1)
'@
    $tmp = Join-Path $env:TEMP ('oapi_val_' + [guid]::NewGuid().ToString('N') + '.py')
    Set-Content -LiteralPath $tmp -Value $code -Encoding UTF8
    & $py $tmp
    $ok = ($LASTEXITCODE -eq 0)
    Remove-Item -LiteralPath $tmp -ErrorAction SilentlyContinue
    $results += [pscustomobject]@{ method='GET'; path='/openapi.json#schema'; code=[int]$open.StatusCode; ok=$ok; msg=if($ok){'ok'}else{'invalid openapi'} }
  } catch { $results += [pscustomobject]@{ method='GET'; path='/openapi.json#schema'; code=0; ok=$false; msg=$_.Exception.Message } }

  # Health payload shape
  try {
    $hj = Invoke-RestMethod -Uri 'http://127.0.0.1:8000/health' -TimeoutSec 5
    $ok = ($hj.status -eq 'ok' -and ($hj.version -is [string]) -and $hj.version.Length -gt 0)
    $results += [pscustomobject]@{ method='GET'; path='/health#schema'; code=200; ok=$ok; msg=if($ok){'ok'}else{'status!=ok or version missing'} }
  } catch { $results += [pscustomobject]@{ method='GET'; path='/health#schema'; code=0; ok=$false; msg=$_.Exception.Message } }

  # JWKS payload shape
  try {
    $jw = Invoke-RestMethod -Uri 'http://127.0.0.1:8000/.well-known/jwks.json' -TimeoutSec 5
    $k = $jw.keys[0]
    $ok = ($jw.keys.Count -ge 1 -and $k.kty -eq 'OKP' -and $k.crv -eq 'Ed25519' -and ($k.x -is [string]))
    $results += [pscustomobject]@{ method='GET'; path='/.well-known/jwks.json#schema'; code=200; ok=$ok; msg=if($ok){'ok'}else{'invalid jwks'} }
  } catch { $results += [pscustomobject]@{ method='GET'; path='/.well-known/jwks.json#schema'; code=0; ok=$false; msg=$_.Exception.Message } }

  # FIN measure payload shape
  try {
    $fm = Invoke-RestMethod -Method Post -Uri 'http://127.0.0.1:8000/v1/fin/alpha/measure' -TimeoutSec 8 -ContentType 'application/json' -Body '{"signals":{"risk":0.1,"sentiment":0.6}}'
    $ok = (($fm.outcome -is [string]) -and ($fm.p -is [double] -or $fm.p -is [decimal] -or $fm.p -is [int]))
    $results += [pscustomobject]@{ method='POST'; path='/v1/fin/alpha/measure#schema'; code=200; ok=$ok; msg=if($ok){'ok'}else{'missing outcome/p'} }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/fin/alpha/measure#schema'; code=0; ok=$false; msg=$_.Exception.Message } }

  # QTMP regressions: predistribution sums ~ 1, verdict in basis, commutator(A!=B)==1
  try {
    $basis = @('ALLOW','DENY','ABSTAIN')
    $qinit = Invoke-RestMethod -Method Post -Uri 'http://127.0.0.1:8000/v1/qtm/init_case' -TimeoutSec 8 -ContentType 'application/json' -Body '{"basis":["ALLOW","DENY","ABSTAIN"]}'
    $sum = 0.0; foreach ($it in $qinit.predistribution) { $sum += [double]$it.p }
    $ok = ([math]::Abs($sum - 1.0) -le 1e-3 -and $qinit.predistribution.Count -eq $basis.Count)
    $results += [pscustomobject]@{ method='POST'; path='/v1/qtm/init_case#regression'; code=200; ok=$ok; msg=if($ok){'ok'}else{"bad predistribution sum=$sum"} }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/qtm/init_case#regression'; code=0; ok=$false; msg=$_.Exception.Message } }
  try {
    $qmeas = Invoke-RestMethod -Method Post -Uri 'http://127.0.0.1:8000/v1/qtm/measure' -TimeoutSec 8 -ContentType 'application/json' -Body '{"operator":"W","source":"ui"}'
    $ok = ($basis -contains $qmeas.verdict)
    $results += [pscustomobject]@{ method='POST'; path='/v1/qtm/measure#regression'; code=200; ok=$ok; msg=if($ok){'ok'}else{"verdict=$($qmeas.verdict) not in basis"} }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/qtm/measure#regression'; code=0; ok=$false; msg=$_.Exception.Message } }
  try {
    $comm = Invoke-RestMethod -Method Post -Uri 'http://127.0.0.1:8000/v1/qtm/commutator' -TimeoutSec 8 -ContentType 'application/json' -Body '{"A":"X","B":"Y"}'
    $ok = ([double]$comm.value -eq 1.0)
    $results += [pscustomobject]@{ method='POST'; path='/v1/qtm/commutator#regression'; code=200; ok=$ok; msg=if($ok){'ok'}else{"value=$($comm.value)"} }
  } catch { $results += [pscustomobject]@{ method='POST'; path='/v1/qtm/commutator#regression'; code=0; ok=$false; msg=$_.Exception.Message } }

  # PCO public rid regression: equals requested rid
  try {
    $pub = Invoke-RestMethod -Uri ('http://127.0.0.1:8000/pco/public/' + $rid) -TimeoutSec 8
    $ok = ($pub.rid -eq $rid)
    $results += [pscustomobject]@{ method='GET'; path='/pco/public/{rid}#rid'; code=200; ok=$ok; msg=if($ok){'ok'}else{"rid=$($pub.rid) != $rid"} }
  } catch { $results += [pscustomobject]@{ method='GET'; path='/pco/public/{rid}#rid'; code=0; ok=$false; msg=$_.Exception.Message } }
  try {
    $pub = Invoke-RestMethod -Uri ('http://127.0.0.1:8000/pco/public/' + $rid) -TimeoutSec 8
    $sig = [string]$pub.signature
    $re = '^[A-Za-z0-9_-]+$'
    $ok = ($sig -match $re) -and (-not $sig.Contains('='))
    $results += [pscustomobject]@{ method='GET'; path='/pco/public/{rid}#signature_b64url'; code=200; ok=$ok; msg=if($ok){'ok'}else{"invalid signature format"} }
  } catch { $results += [pscustomobject]@{ method='GET'; path='/pco/public/{rid}#signature_b64url'; code=0; ok=$false; msg=$_.Exception.Message } }
  try {
    $pub = Invoke-RestMethod -Uri ('http://127.0.0.1:8000/pco/public/' + $rid) -TimeoutSec 8
    $root = ''
    if ($pub.PSObject.Properties['ledger']) { $root = [string]$pub.ledger.merkle_root }
    # If not present on public PCO, read the saved file from POST /v1/pco/bundle
    if (-not $root) {
      $pb = Invoke-RestMethod -Method Post -Uri 'http://127.0.0.1:8000/v1/pco/bundle' -TimeoutSec 8 -ContentType 'application/json' -Body $payload
      $pp = [string]$pb.public_path
      $data = Get-Content -LiteralPath $pp -Raw
      $jobj = $data | ConvertFrom-Json
      $root = [string]$jobj.ledger.merkle_root
    }
    $ok = ($root) -and ($root.Length -eq 64) -and ($root -match '^[0-9a-f]+$')
    $results += [pscustomobject]@{ method='GET'; path='/pco/public/{rid}#ledger_merkle_root'; code=200; ok=$ok; msg=if($ok){'ok'}else{"invalid merkle_root"} }
  } catch { $results += [pscustomobject]@{ method='GET'; path='/pco/public/{rid}#ledger_merkle_root'; code=0; ok=$false; msg=$_.Exception.Message } }
} finally {
  Stop-Server $proc
}

# Print details and summary
foreach ($r in $results) {
  $status = if ($r.ok) { 'OK ' } else { 'ERR' }
  Write-Host ("[$($r.method)] $($r.path) => $status ($($r.code)) $($r.msg)")
}
$arr = @($results)
$total = $arr.Count
$passes = ($arr | Where-Object { $_.ok }).Count
$fails = $total - $passes
# Compute p95 from /metrics histogram (certeus_http_request_duration_ms_bucket)
$p95 = 'n/a'
try {
  $m = Invoke-WebRequest -UseBasicParsing -Uri 'http://127.0.0.1:8000/metrics' -TimeoutSec 5
  $lines = ($m.Content -split "`n")
  $buckets = @{}
  foreach ($ln in $lines) {
    if ($ln -match '^certeus_http_request_duration_ms_bucket\{[^}]*le="([^"]+)"[^}]*\}\s+([0-9\.eE\+\-]+)\s*$') {
      $leStr = $Matches[1]
      $cnt = [double]::Parse($Matches[2], [Globalization.CultureInfo]::InvariantCulture)
      if ($buckets.ContainsKey($leStr)) { $buckets[$leStr] += $cnt } else { $buckets[$leStr] = $cnt }
    }
  }
  if ($buckets.Count -gt 0) {
    $entries = @()
    foreach ($k in $buckets.Keys) {
      $num = if ($k -eq '+Inf') { [double]::PositiveInfinity } else { [double]::Parse($k, [Globalization.CultureInfo]::InvariantCulture) }
      $entries += [pscustomobject]@{ le=$k; num=$num; cnt=$buckets[$k] }
    }
    $entries = $entries | Sort-Object -Property num
    $totalCount = ($entries | Where-Object { $_.le -eq '+Inf' } | Select-Object -First 1).cnt
    if (-not $totalCount) { $totalCount = ($entries | Select-Object -Last 1).cnt }
    $threshold = 0.95 * $totalCount
    $cum = 0.0
    foreach ($e in $entries) {
      if ($e.le -eq '+Inf') { continue }
      $cum += $e.cnt
      if ($cum -ge $threshold) { $p95 = [string]::Format([Globalization.CultureInfo]::InvariantCulture, '{0:0.###}', $e.num); break }
    }
  }
} catch { }

# Optional SLO threshold enforcement
$sloThresh = $env:SLO_MAX_P95_MS
if ($sloThresh -and $p95 -ne 'n/a') {
  try {
    $p95num = [double]::Parse($p95, [Globalization.CultureInfo]::InvariantCulture)
    $thrnum = [double]::Parse($sloThresh, [Globalization.CultureInfo]::InvariantCulture)
    if ($p95num -gt $thrnum) {
      Write-Host ("SLO VIOLATION: p95_ms=$p95num > threshold_ms=$thrnum") -ForegroundColor Red
      $fails += 1
    }
  } catch { }
}

# Optional failure budget (max allowed fails)
$maxFails = 0
try {
  if ($env:SMOKE_MAX_FAILS) { $maxFails = [int]$env:SMOKE_MAX_FAILS }
} catch { $maxFails = 0 }

# Ensure reports dir, write JSON summary
try { New-Item -ItemType Directory -Force -Path reports | Out-Null } catch { }
$summaryObj = [pscustomobject]@{ total=$total; passes=$passes; fails=$fails; p95_ms=$p95; threshold_ms=$sloThresh; max_fails=$maxFails }
$summaryJson = $summaryObj | ConvertTo-Json -Depth 3
Set-Content -LiteralPath 'reports\smoke_summary.json' -Value $summaryJson -Encoding UTF8

# Append GitHub step summary if available
if ($env:GITHUB_STEP_SUMMARY) {
  Add-Content -LiteralPath $env:GITHUB_STEP_SUMMARY -Value "### Smoke Summary`n`n- total: $total`n- passes: $passes`n- fails: $fails`n- p95_ms: $p95`n- threshold_ms: $sloThresh`n"
}

Write-Host ("SMOKE SUMMARY: total=$total passes=$passes fails=$fails p95_ms=$p95 threshold_ms=$sloThresh max_fails=$maxFails")
if ($fails -gt $maxFails) { exit 1 } else { exit 0 }
