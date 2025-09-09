Param(
  [switch]$Force
)

$ErrorActionPreference = 'Stop'

function Ensure-FileLine {
  param([string]$Path,[string]$Line)
  if (-not (Test-Path -LiteralPath $Path)) { New-Item -ItemType File -Path $Path -Force | Out-Null }
  $content = Get-Content -LiteralPath $Path -ErrorAction SilentlyContinue
  if ($null -eq $content) { $content = @() }
  if (-not ($content -contains $Line)) { Add-Content -LiteralPath $Path -Value $Line }
}

$UserHome = [Environment]::GetFolderPath('UserProfile')
$GlobalIgnore = Join-Path $UserHome '.gitignore_global'
Ensure-FileLine -Path $GlobalIgnore -Line 'AGENT.md'
Ensure-FileLine -Path $GlobalIgnore -Line '.env'
Ensure-FileLine -Path $GlobalIgnore -Line '.env.example'
Ensure-FileLine -Path $GlobalIgnore -Line '.control/'
git config --global core.excludesFile $GlobalIgnore | Out-Null

$GlobalHooks = Join-Path $UserHome '.hooks'
New-Item -ItemType Directory -Force -Path $GlobalHooks | Out-Null

$PreCommit = @'
#!/usr/bin/env bash
set -euo pipefail
A=$(printf '\x41\x47\x45\x4e\x54\x2e\x6d\x64')
E=$(printf '\x2e\x65\x6e\x76')
EE=$(printf '\x2e\x65\x6e\x76\x2e\x65\x78\x61\x6d\x70\x6c\x65')
C=$(printf '\x2e\x63\x6f\x6e\x74\x72\x6f\x6c\x2f')
PAT="((^|/)$A$|(^|/)$E$|(^|/)$EE$|(^|/)$C)"
STAGED=$(git diff --cached --name-only 2>/dev/null || true)
if printf '%s\n' "$STAGED" | grep -E -q "$PAT"; then
  echo "ERROR: Zablokowano commit plików wewnętrznych (AGENT.md, .env, .env.example, .control/)." >&2
  exit 1
fi
exit 0
'@

$PrePush = @'
#!/usr/bin/env bash
set -euo pipefail
A=$(printf '\x41\x47\x45\x4e\x54\x2e\x6d\x64')
E=$(printf '\x2e\x65\x6e\x76')
EE=$(printf '\x2e\x65\x6e\x76\x2e\x65\x78\x61\x6d\x70\x6c\x65')
C=$(printf '\x2e\x63\x6f\x6e\x74\x72\x6f\x6c\x2f')
PAT="((^|/)$A$|(^|/)$E$|(^|/)$EE$|(^|/)$C)"
BLOCK=0
while read -r local_ref local_sha remote_ref remote_sha; do
  [ -z "${local_sha:-}" ] && continue
  [ "$local_sha" = "0000000000000000000000000000000000000000" ] && continue
  RANGE="$local_sha"
  if [ -n "${remote_sha:-}" ] && [ "$remote_sha" != "0000000000000000000000000000000000000000" ]; then
    RANGE="${remote_sha}..${local_sha}"
  fi
  NAMES=$(git log --pretty='' --name-only --no-merges $RANGE | sort -u || true)
  if printf '%s\n' "$NAMES" | grep -E -q "$PAT"; then
    BLOCK=1
  fi
done
if [ "$BLOCK" -eq 1 ]; then
  echo "ERROR: Zablokowano push — w historii znajdują się pliki wewnętrzne." >&2
  exit 1
fi
exit 0
'@

Set-Content -LiteralPath (Join-Path $GlobalHooks 'pre-commit') -Value $PreCommit -NoNewline
Set-Content -LiteralPath (Join-Path $GlobalHooks 'pre-push') -Value $PrePush -NoNewline
git config --global core.hooksPath $GlobalHooks | Out-Null

Write-Host "Skonfigurowano:" -ForegroundColor Green
Write-Host "- core.excludesFile = $GlobalIgnore"
Write-Host "- core.hooksPath   = $GlobalHooks"
