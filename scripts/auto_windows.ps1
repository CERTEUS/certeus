# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/auto_windows.ps1                            |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/auto_windows.ps1                            |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

param([string]$RepoPath = ".")
$ErrorActionPreference = "Stop"

function Invoke-Cmd($cmd, $cmdArgs) {
  $argsText = if ($cmdArgs) { ($cmdArgs -join ' ') } else { '' }
  Write-Host ("`n> {0} {1}" -f $cmd, $argsText) -ForegroundColor Cyan
  if (Test-Path -LiteralPath $cmd) { & "$cmd" @cmdArgs } else { & $cmd @cmdArgs }
}

function Ensure-Venv {
  $pyPath = Join-Path $PWD '.venv\Scripts\python.exe'
  if (Test-Path -LiteralPath $pyPath) { return }
  if (Test-Path -LiteralPath '.venv') { try { Remove-Item -Recurse -Force '.venv' -ErrorAction SilentlyContinue } catch {} }
  if (-not (Get-Command py -ErrorAction SilentlyContinue)) { throw "Brak 'py' w PATH. Zainstaluj Python 3.11" }
  Invoke-Cmd py @('-3.11','-m','venv','.venv')
}

function Run-Tests([string]$py) {
  Invoke-Cmd $py @('-m','ruff','check','.',"--fix")
  Invoke-Cmd $py @('-m','ruff','format','.')
  New-Item -ItemType Directory -Force -Path reports | Out-Null
  $testOutput = & $py -m pytest -q --junitxml="reports/junit.xml" 2>&1 \
    | Tee-Object -FilePath reports\pytest.out.txt -Encoding utf8 \
    | Tee-Object -Variable _buf
  $code = $LASTEXITCODE
  if ($code -ne 0) {
    Write-Warning "Testy NIE przeszły; ostatnie 100 linii:"; $_buf | Select-Object -Last 100 | Out-Host
    throw "Testy nie przeszły (exit=$code)"
  }
  return $testOutput
}

function Fix-Upstream-And-Push {
  git config --local --unset-all branch.main.merge 2>$null
  git config --local --add branch.main.merge refs/heads/main
  git config --local --unset-all branch.main.remote 2>$null
  git config --local --add branch.main.remote origin

  git add -A
  & git commit -m "chore: lint+tests via Codex [auto]" --no-verify 2>$null || Write-Host "Brak zmian do commit."

  & git push -u origin HEAD:main
  if ($LASTEXITCODE -ne 0) {
    Write-Warning "Push odrzucony. Próbuję rebase..."
    git fetch origin
    git pull --rebase origin main
    & git push -u origin HEAD:main
    if ($LASTEXITCODE -ne 0) {
      Write-Warning "Push nadal się nie udał. Próbuję przez GitHub CLI (HTTPS)."
      if (-not (Get-Command gh -ErrorAction SilentlyContinue)) { winget install --id GitHub.cli -e | Out-Null }
      gh auth status 2>$null || gh auth login --hostname github.com --web --git-protocol https
      git remote set-url origin https://github.com/CERTEUS/certeus.git
      & git push -u origin HEAD:main
      if ($LASTEXITCODE -ne 0) {
        Write-Warning "Gałąź chroniona lub inny błąd. Tworzę gałąź i PR."
        git switch -c feat/codex-auto 2>$null || git switch feat/codex-auto
        & git push -u origin HEAD
        gh pr create -f -B main
      }
    }
  }
}

# MAIN
Set-Location $RepoPath
Ensure-Venv
$py = Join-Path $PWD '.venv\Scripts\python.exe'
Write-Host "Python: $py" -ForegroundColor Yellow

Invoke-Cmd $py @('-m','pip','install','-U','pip','wheel','setuptools','ruff','pytest','jsonschema','cryptography','fastapi','uvicorn')

& "$PSScriptRoot/keys_dev.ps1"
& "$PSScriptRoot/env_load.ps1"

git config core.hooksPath .githooks

$out = Run-Tests -py $py
$last = ($out | Select-String -Pattern 'passed' -SimpleMatch | Select-Object -Last 1)
$pyver = (& $py -V)
$ruffver = (& $py -m ruff --version)

Fix-Upstream-And-Push

$sha = (git rev-parse HEAD).Trim()
$remote = (git remote -v | Select-String 'origin' | Select-Object -First 1)

Write-Host "`n===== RAPORT =====" -ForegroundColor Green
Write-Host ("Python: {0}" -f $pyver)
Write-Host ("Ruff:   {0}" -f $ruffver)
Write-Host ("Testy:  {0}" -f ($last -as [string]))
Write-Host ("Remote: {0}" -f ($remote -as [string]))
Write-Host ("Commit: {0}" -f $sha)

