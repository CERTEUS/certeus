#!/usr/bin/env pwsh
# +-------------------------------------------------------------+
# |                          CERTEUS                            |
# +-------------------------------------------------------------+
# | FILE: scripts/github/seed_labels.ps1                       |
# | ROLE: Project script.                                        |
# | PLIK: scripts/github/seed_labels.ps1                       |
# | ROLA: Skrypt projektu.                                       |
# +-------------------------------------------------------------+

Param()

$ErrorActionPreference = 'Continue'

$labels = @(
  @{ name = 'area/api'; color = '1f77b4'; description = 'API surface / OpenAPI' },
  @{ name = 'area/ui'; color = 'ff7f0e'; description = 'UI / Frontend' },
  @{ name = 'area/core'; color = '2ca02c'; description = 'Core engine' },
  @{ name = 'area/infra'; color = '9467bd'; description = 'Infrastructure / CI' },
  @{ name = 'type/bug'; color = 'd62728'; description = 'Bug' },
  @{ name = 'type/feature'; color = '17becf'; description = 'Feature request' },
  @{ name = 'type/question'; color = '8c564b'; description = 'Question' },
  @{ name = 'type/proposal'; color = '7f7f7f'; description = 'Design proposal' },
  @{ name = 'priority/p0'; color = 'e377c2'; description = 'Critical' },
  @{ name = 'priority/p1'; color = 'bcbd22'; description = 'High' },
  @{ name = 'priority/p2'; color = '7f7f7f'; description = 'Medium' },
  @{ name = 'priority/p3'; color = 'c7c7c7'; description = 'Low' }
)

foreach ($l in $labels) {
  gh label create $l.name --color $l.color --description $l.description 2>$null
}

Write-Output "Labels seeded."

