# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/release/tag_release.ps1                      |
# | ROLE: Project script.                                        |
# | PLIK: scripts/release/tag_release.ps1                      |
# | ROLA: Tagowanie wydania i push tagu (Windows/PowerShell).    |
# +-------------------------------------------------------------+

param(
  [string]$Version = "v1.0.0"
)

Write-Host "Creating annotated tag $Version"
git tag -a $Version -m "Release $Version"

Write-Host "Pushing tag $Version"
git push origin $Version

Write-Host "Done."

