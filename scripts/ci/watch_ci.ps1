# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/ci/watch_ci.ps1                               |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/ci/watch_ci.ps1                               |
# | ROLA: Skrypt PowerShell.                                    |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===

param(
  [string]$Branch = "work/daily",
  [string]$Workflow = "",
  [int]$Interval = 30,
  [switch]$Once
)

$ErrorActionPreference = "Stop"

# === KONFIGURACJA / CONFIGURATION ===

function Get-GitHubToken {
  if ($env:GITHUB_TOKEN) { return ($env:GITHUB_TOKEN).Trim() }
  if ($env:ADMIN_TOKEN) { return ($env:ADMIN_TOKEN).Trim() }
  try {
    $p = Join-Path $PWD ".devkeys/admin_token.txt"
    if (Test-Path $p) { return (Get-Content $p -Raw).Trim() }
  } catch {}
  try {
    $out = & gh auth token 2>$null
    if ($LASTEXITCODE -eq 0) {
      $cand = ($out | Out-String).Trim()
      if ($cand) { return $cand }
    }
  } catch {}
  return $null
}

function Get-RepoSlug {
  try {
    $origin = git remote get-url origin 2>$null
    if ($origin -and ($origin -match 'github.com[:/](.*?)/(.*?)(\.git)?$')) {
      return "$($matches[1])/$($matches[2])"
    }
  } catch {}
  return "CERTEUS/certeus"
}

# === LOGIKA / LOGIC ===

function Show-CiStatus {
  param(
    [string]$Token,
    [string]$RepoSlug,
    [string]$Branch,
    [string]$Workflow
  )

  $h = @{ Authorization = "token $Token"; 'User-Agent' = 'certeus-ci-watch'; 'X-GitHub-Api-Version' = '2022-11-28' }

  if ($Workflow) {
    $uri = "https://api.github.com/repos/$RepoSlug/actions/workflows/$Workflow/runs?branch=$Branch&per_page=10"
  } else {
    $uri = "https://api.github.com/repos/$RepoSlug/actions/runs?branch=$Branch&per_page=10"
  }

  $resp = Invoke-RestMethod -Headers $h -Uri $uri -Method GET
  $runs = @($resp.workflow_runs)
  if (-not $runs -or $runs.Count -eq 0) {
    Write-Host "No runs found for $RepoSlug@$Branch" -ForegroundColor Yellow
    return
  }

  $ts = Get-Date -Format 'u'
  Write-Host "[$ts] CI status for $RepoSlug@$Branch" -ForegroundColor Cyan

  $table = $runs | Select-Object name, head_branch, status, conclusion, run_number, head_sha, created_at
  $table | Format-Table -AutoSize

  $succ = ($runs | Where-Object { $_.conclusion -eq 'success' }).Count
  $fail = ($runs | Where-Object { $_.conclusion -eq 'failure' }).Count
  $prog = ($runs | Where-Object { $_.status -ne 'completed' }).Count
  Write-Host ("Summary: success={0} failure={1} in_progress={2}" -f $succ, $fail, $prog)

  # If filtering by a workflow, print last job steps for the latest run
  if ($Workflow -and $runs[0]) {
    $rid = $runs[0].id
    try {
      $jobs = Invoke-RestMethod -Headers $h -Uri "https://api.github.com/repos/$RepoSlug/actions/runs/$rid/jobs"
      $job = $jobs.jobs | Select-Object -First 1
      if ($job) {
        Write-Host ("Last job: {0} → {1}" -f $job.name, $job.conclusion)
        $job.steps | Select-Object name, conclusion | Format-Table -AutoSize
      }
    } catch {}
  }
}

# === I/O / ENDPOINTS ===

$token = Get-GitHubToken
if (-not $token) { throw "Missing token: set GITHUB_TOKEN/ADMIN_TOKEN or provide .devkeys/admin_token.txt" }

$slug = Get-RepoSlug

do {
  try {
    Show-CiStatus -Token $token -RepoSlug $slug -Branch $Branch -Workflow $Workflow
  } catch {
    Write-Warning $_.Exception.Message
  }
  if ($Once) { break }
  Start-Sleep -Seconds $Interval
} while ($true)

# === TESTY / TESTS ===
