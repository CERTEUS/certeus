# CERTEUS — Bootstrap GitHub self-hosted runner (Windows) + Dokan
# Run in elevated PowerShell. Requires GH CLI (or will install via winget), Chocolatey for Dokan install.

param(
  [string]$RepoSlug = "CERTEUS/certeus",
  [string]$RunnerVersion = "2.315.0",
  [string]$Labels = "self-hosted,windows,dokan",
  [string]$RunnerDir = "$env:USERPROFILE\actions-runner"
)

Write-Host "[+] Preparing directory: $RunnerDir"
New-Item -ItemType Directory -Force -Path $RunnerDir | Out-Null
Set-Location $RunnerDir

if (-not (Get-Command gh -ErrorAction SilentlyContinue)) {
  Write-Host "[+] Installing GitHub CLI via winget"
  winget install --id GitHub.cli -e -h 2>$null | Out-Null
}

Write-Host "[+] Fetching registration token via gh api"
$regToken = gh api -X POST "repos/$RepoSlug/actions/runners/registration-token" --jq ".token"

Write-Host "[+] Downloading runner v$RunnerVersion"
$zip = "actions-runner-win-x64-$RunnerVersion.zip"
Invoke-WebRequest -Uri "https://github.com/actions/runner/releases/download/v$RunnerVersion/$zip" -OutFile $zip
Add-Type -AssemblyName System.IO.Compression.FileSystem
[System.IO.Compression.ZipFile]::ExtractToDirectory($zip, "$RunnerDir", $true)

Write-Host "[+] Configuring runner (labels: $Labels)"
& .\config.cmd --url "https://github.com/$RepoSlug" --token "$regToken" --labels "$Labels" --unattended

if (-not (Get-Command choco -ErrorAction SilentlyContinue)) {
  Write-Host "[+] Installing Chocolatey"
  Set-ExecutionPolicy Bypass -Scope Process -Force
  [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
  Invoke-Expression ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))
}

Write-Host "[+] Installing Dokan (LTS)"
choco install dokan-lts -y || Write-Warning "Dokan install may require reboot"

Write-Host "[+] Installing and starting runner as service"
& .\svc install
& .\svc start
Write-Host "[OK] Windows runner ready with labels: $Labels"

