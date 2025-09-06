@echo off
REM ============================================================================
REM CERTEUS - Windows Environment Setup Script
REM ============================================================================
REM PL: Skrypt konfiguracji środowiska dla Windows
REM EN: Windows environment setup script
REM ============================================================================

echo ============================================================================
echo 🚀 CERTEUS - Windows Environment Setup
echo ============================================================================

REM Check if Python is installed
python --version >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ Python not found. Please install Python 3.11+ from python.org
    pause
    exit /b 1
)

echo ✅ Python found:
python --version

REM Check if Git is installed
git --version >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ Git not found. Please install Git from git-scm.com
    pause
    exit /b 1
)

echo ✅ Git found:
git --version

REM Create virtual environment
if not exist ".venv" (
    echo 📦 Creating virtual environment...
    python -m venv .venv
    echo ✅ Virtual environment created
) else (
    echo 📦 Virtual environment already exists
)

REM Activate virtual environment
echo 🔧 Activating virtual environment...
call .venv\Scripts\activate.bat

REM Upgrade pip
echo 📦 Upgrading pip...
python -m pip install --upgrade pip

REM Install dependencies
if exist "requirements.txt" (
    echo 📦 Installing dependencies...
    pip install -r requirements.txt
    echo ✅ Dependencies installed
)

REM Check if VS Code is installed
code --version >nul 2>&1
if %errorlevel% neq 0 (
    echo ⚠️  VS Code not found. Install from code.visualstudio.com for best experience
) else (
    echo ✅ VS Code found:
    code --version | findstr /C:"Version"

    echo 🔧 Installing VS Code extensions...
    code --install-extension ms-python.python
    code --install-extension ms-python.vscode-pylance
    code --install-extension charliermarsh.ruff
    code --install-extension github.copilot
    echo ✅ Essential extensions installed
)

REM Health check
echo.
echo 🎯 Environment Health Check:
echo ✅ Python:
python --version
echo ✅ Virtual environment: %CD%\.venv
echo ✅ Pylance config: pyrightconfig.json
if exist "pyrightconfig.json" (
    echo ✅ Pylance optimized for performance
) else (
    echo ⚠️  Pylance config missing
)

echo.
echo 🎉 Setup completed successfully!
echo.
echo 🎯 Next steps:
echo    1. Activate environment: .venv\Scripts\activate.bat
echo    2. Open VS Code: code .
echo    3. Start coding!
echo.
pause
