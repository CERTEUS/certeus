@echo off
REM Simple shim to invoke the active Python interpreter as "python3"
REM Prefer venv if present; fallback to system python

SETLOCAL ENABLEEXTENSIONS
SET VENV_PY="%~dp0\.venv\Scripts\python.exe"

IF EXIST %VENV_PY% (
  %VENV_PY% %*
) ELSE (
  python %*
)

EXIT /B %ERRORLEVEL%

