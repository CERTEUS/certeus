# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/server.ps1                                  |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/server.ps1                                  |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===
# === KONFIGURACJA / CONFIGURATION ===
# === LOGIKA / LOGIC ===
# === I/O / ENDPOINTS ===
# === TESTY / TESTS ===

param()
$ErrorActionPreference = "Stop"
& "$PSScriptRoot/env_load.ps1"
$py = "$PWD\.venv\Scripts\python.exe"
# Użycie / Usage:
#   pwsh -File .\scripts\server.ps1
# Wymagania: aktywny venv (.venv) i zależności (fastapi, uvicorn, python-multipart)
Write-Host "Start serwera: http://127.0.0.1:8000" -ForegroundColor Yellow
& $py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000


