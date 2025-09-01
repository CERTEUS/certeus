# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/server.ps1                                  |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/server.ps1                                  |
# | ROLA: Skrypt PowerShell.                                     |
# +-------------------------------------------------------------+

param()
$ErrorActionPreference = "Stop"
& "$PSScriptRoot/env_load.ps1"
$py = "$PWD\.venv\Scripts\python.exe"
Write-Host "Startuję serwer: http://127.0.0.1:8000" -ForegroundColor Yellow
& $py -m uvicorn services.api_gateway.main:app --host 127.0.0.1 --port 8000

