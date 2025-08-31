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

