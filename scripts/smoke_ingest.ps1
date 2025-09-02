# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/smoke_ingest.ps1                            |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/smoke_ingest.ps1                            |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |                 Smoke test for /v1/ingest                   |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# Files live only in working dir; we do not git-add them.
Set-Content -NoNewline -Encoding ASCII .\sample.txt 'hello CERTEUS'
Set-Content -NoNewline -Encoding ASCII .\sample.pdf '%PDF-1.4 dummy'

Write-Host "[INFO] Health"
curl.exe -sS http://127.0.0.1:8000/health

Write-Host "[INFO] Ingest TXT"
curl.exe -sS -i --form "file=@sample.txt;type=text/plain" http://127.0.0.1:8000/v1/ingest | Select-String -Pattern "HTTP/1.1 200"

Write-Host "[INFO] Ingest PDF"
curl.exe -sS -i --form "file=@sample.pdf;type=application/pdf" http://127.0.0.1:8000/v1/ingest | Select-String -Pattern "HTTP/1.1 200"

Write-Host "[INFO] Done"
