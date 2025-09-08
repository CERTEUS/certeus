Param()

$ErrorActionPreference = 'Stop'

try {
  & code --install-extension streetsidesoftware.code-spell-checker --force | Out-Null
  & code --install-extension streetsidesoftware.code-spell-checker-polish --force | Out-Null
  & code --install-extension DavidAnson.vscode-markdownlint --force | Out-Null
} catch {
  Write-Warning "Nie udało się wywołać 'code' (CLI VS Code). Upewnij się, że VS Code dodał CLI do PATH."
}

$userSettings = Join-Path $env:APPDATA 'Code\User\settings.json'
if (-not (Test-Path -LiteralPath $userSettings)) {
  New-Item -ItemType File -Path $userSettings -Force | Out-Null
  Set-Content -LiteralPath $userSettings -Value '{}' -NoNewline
}

$json = Get-Content -LiteralPath $userSettings -Raw | ConvertFrom-Json -ErrorAction SilentlyContinue
if ($null -eq $json) { $json = [ordered]@{} }

$json.'cSpell.language' = 'en,pl'
$json.'cSpell.enabledLanguageIds' = @('markdown','plaintext','git-commit')
$json.'cSpell.diagnosticLevel' = 'Information'

$json | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath $userSettings -NoNewline

Write-Host 'Skonfigurowano globalne cSpell i markdownlint w VS Code.' -ForegroundColor Green
