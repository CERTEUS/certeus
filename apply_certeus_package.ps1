# ┌──────────────────────────────────────────────────────────────┐
# │                         CERTEUS                              │
# │          Apply certeus-package.zip into local repo           │
# └──────────────────────────────────────────────────────────────┘
# Opis (PL): Skrypt PowerShell do bezpiecznego nadpisania plików w repo (branch, backup, unzip).
# Description (EN): PowerShell script to safely overlay ZIP onto your repo (branch, backup, unzip).
# File: scripts/apply_certeus_package.ps1 | Author: Radosław Skarżycki (Radziu) | Version: 1.0 | Date: 2025-08-30T10:54:18Z | License: MIT

param(
    [string]$RepoPath = "F:\projekty\certeus",
    [string]$ZipPath  = "F:\projekty\certeus\certeus-package.zip",
    [string]$Branch   = "chore/apply-certeus-package"
)

Write-Host "RepoPath: $RepoPath" -ForegroundColor Cyan
Write-Host "ZipPath : $ZipPath" -ForegroundColor Cyan
Write-Host "Branch  : $Branch" -ForegroundColor Cyan

if (!(Test-Path $RepoPath)) {{ Write-Error "RepoPath not found: $RepoPath"; exit 1 }}
if (!(Test-Path (Join-Path $RepoPath '.git'))) {{ Write-Error "Not a git repo: $RepoPath\.git missing"; exit 1 }}
if (!(Test-Path $ZipPath)) {{ Write-Error "ZipPath not found: $ZipPath"; exit 1 }}

function Invoke-Git {{ param([string[]]$Args) git -C $RepoPath @Args }}

# 1) Save checkpoint on current branch
try {{ Invoke-Git @('add','-A') | Out-Null }} catch {{}}
try {{ Invoke-Git @('commit','-m','chore: checkpoint before applying certeus-package') | Out-Null }} catch {{ Write-Host "No changes to commit (checkpoint)" }}

# 2) Create a working branch
try {{ Invoke-Git @('switch','-c',$Branch) | Out-Null }} catch {{ Invoke-Git @('checkout','-b',$Branch) | Out-Null }}

# 3) Extract ZIP over the repo (overwrite)
try {{
    Write-Host "Extracting ZIP with Expand-Archive..." -ForegroundColor Yellow
    Expand-Archive -Path $ZipPath -DestinationPath $RepoPath -Force
}} catch {{
    Write-Warning "Expand-Archive failed, falling back to 'tar'..."
    & tar -xf $ZipPath -C $RepoPath
}}

# 4) Show what changed
Invoke-Git @('status','-s')

# 5) Optionally fix README badge placeholder (ORG/REPO) – uncomment & edit:
# (Get-Content (Join-Path $RepoPath 'README.md')) -replace 'ORG/REPO','CERTEUS/certeus' | Set-Content (Join-Path $RepoPath 'README.md') -NoNewline

# 6) Stage and commit changes
Invoke-Git @('add','-A')
Invoke-Git @('commit','-m','feat: apply certeus-package (assets, docs, infra, CI)')

Write-Host "Done. Review changes, then push:" -ForegroundColor Green
Write-Host "  git -C `"$RepoPath`" push -u origin $Branch" -ForegroundColor Green

# 7) (Optional) Local run commands for Windows PowerShell
Write-Host "`nLocal run hints:" -ForegroundColor Cyan
Write-Host "  uv venv"
Write-Host "  .\.venv\Scripts\Activate.ps1"
Write-Host "  uv pip install -r requirements.txt"
Write-Host "  docker compose -f infra\docker-compose.dev.yml up -d --build"
Write-Host "  python -m uvicorn services.proofgate.app:app --reload --port 8081"
