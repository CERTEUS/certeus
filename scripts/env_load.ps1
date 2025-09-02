# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/env_load.ps1                                |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/env_load.ps1                                |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

param([string]$FilePath = ".env")
if (!(Test-Path $FilePath)) { return }
$pairs = Get-Content $FilePath | Where-Object { $_ -and ($_ -notmatch '^\s*#') }
foreach ($p in $pairs) {
  $kv = $p -split '=', 2
  if ($kv.Length -eq 2) { [Environment]::SetEnvironmentVariable($kv[0], $kv[1]) }
}
$pemPath = [Environment]::GetEnvironmentVariable("ED25519_PRIVKEY_PEM_PATH")
if ($pemPath -and (Test-Path $pemPath)) {
  $pem = Get-Content $pemPath -Raw
  [Environment]::SetEnvironmentVariable("ED25519_PRIVKEY_PEM", $pem)
}
$pubdir = [System.IO.Path]::Combine($PWD, ([Environment]::GetEnvironmentVariable("PROOF_BUNDLE_DIR") ?? "data\public_pco"))
New-Item -ItemType Directory -Force -Path $pubdir | Out-Null
Write-Host "OK: załadowano .env i ustawiono zmienne środowiskowe."

# --- GitHub git auth (permanent) ----------------------------------------------
# Wykorzystaj .devkeys/{github_user.txt,admin_token.txt} do zapisania
# poświadczeń w ~/.git-credentials oraz ustaw helper=store (idempotentnie),
# aby nowe sesje nie wymagały ręcznej konfiguracji.
try {
  $userFile = Join-Path $PWD ".devkeys/github_user.txt"
  $tokFile  = Join-Path $PWD ".devkeys/admin_token.txt"
  if ((Test-Path $userFile) -and (Test-Path $tokFile)) {
    $usr = (Get-Content $userFile -Raw).Trim()
    $tok = (Get-Content $tokFile  -Raw).Trim()
    $userProfile = [Environment]::GetFolderPath('UserProfile')
    $credPath = Join-Path $userProfile ".git-credentials"
    # Dopisz wpis host-level i repo-level (idempotentnie)
    # Uwaga: unikamy interpolacji z ":" — składamy łańcuchy konkatenacją.
    $hostLine = 'https://' + $usr + ':' + $tok + '@github.com'
    $repoLine = 'https://' + $usr + ':' + $tok + '@github.com/CERTEUS/certeus.git'
    if (Test-Path $credPath) {
      $cur = Get-Content $credPath -Raw
      if ($cur -notmatch [regex]::Escape($hostLine)) { Add-Content $credPath $hostLine }
      if ($cur -notmatch [regex]::Escape($repoLine)) { Add-Content $credPath $repoLine }
    } else {
      Set-Content $credPath -Value ($hostLine + "`n" + $repoLine) -Encoding UTF8
    }
    git config --global credential.helper store | Out-Null
    git config --global credential.useHttpPath true | Out-Null
    Write-Host "OK: zaktualizowano ~/.git-credentials i helper=store (GitHub)."
  }
} catch { Write-Warning "GitHub git auth setup skipped: $($_.Exception.Message)" }

