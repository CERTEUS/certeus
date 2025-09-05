# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/bootstrap.ps1                                 |
# | ROLE: PowerShell script.                                    |
# | PLIK: scripts/bootstrap.ps1                                 |
# | ROLA: Skrypt PowerShell.                                    |
# +-------------------------------------------------------------+

# === IMPORTY / IMPORTS ===

# === KONFIGURACJA / CONFIGURATION ===

param()
$ErrorActionPreference = "Stop"

# === LOGIKA / LOGIC ===

Write-Host "[bootstrap] Checking Python runtimes..."

$pyExe = $null
$uvPy = Join-Path $env:APPDATA 'uv/python/cpython-3.11.9-windows-x86_64-none/python.exe'

if (Test-Path $uvPy) {
  $pyExe = $uvPy
} elseif (Get-Command py -ErrorAction SilentlyContinue) {
  try { & py -0p | Out-Null; $pyExe = 'py' } catch { $pyExe = $null }
}
if (-not $pyExe) {
  if (Get-Command python -ErrorAction SilentlyContinue) {
    $pyExe = 'python'
  }
}
if (-not $pyExe) {
  throw "No Python runtime found. Please install Python 3.11+ or set up uv-managed Python."
}

Write-Host "[bootstrap] Using Python: $pyExe"

$venvPy = '.venv_cli/Scripts/python.exe'
if (-not (Test-Path $venvPy)) {
  Write-Host "[bootstrap] Creating venv at .venv_cli"
  & $pyExe -m venv .venv_cli
}

if (-not (Test-Path $venvPy)) {
  throw "Virtualenv not created: $venvPy"
}

& $venvPy -V

Write-Host "[bootstrap] Upgrading pip/wheel/setuptools and installing dev deps"

& $venvPy -m pip install -U pip wheel setuptools |
  Where-Object { $_ -ne $null } | Out-Null

$pkgs = @(
  'ruff', 'pytest', 'jsonschema', 'cryptography', 'fastapi', 'uvicorn', 'pre-commit',
  'httpx', 'prometheus_client', 'python-multipart', 'z3-solver', 'requests', 'hypothesis', 'pytest-asyncio'
)

& $venvPy -m pip install @pkgs |
  Where-Object { $_ -ne $null } | Out-Null

Write-Host "[bootstrap] Running ruff (check + format)"
& $venvPy -m ruff check . --fix
& $venvPy -m ruff format .

Write-Host "[bootstrap] Running pytest (quick)"
New-Item -ItemType Directory -Force -Path reports | Out-Null
& $venvPy -m pytest -q

Write-Host "[bootstrap] OK: environment ready (.venv_cli)"

# === I/O / ENDPOINTS ===

# === TESTY / TESTS ===
