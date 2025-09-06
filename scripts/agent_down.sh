# ============================================================================
#  CODESPACES macOS RUNNER PACK  |  ForgeHeader v1
#  PL: Zestaw do postawienia self-hosted runnera macOS z poziomu Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, rejestracja runnera przez GH API.
#  EN: End-to-end self-hosted macOS runner from Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, runner registration via GH API.
#
#  File      : scripts/agent_down.sh
#  Author    : Radosław Skarżycki (Radziu)
#  Version   : 0.2.0
#  Date (UTC): 2025-09-06T17:40:49Z
#  License   : MIT
#  Repo      : <fill-after-commit>
# ============================================================================

#!/usr/bin/env bash
set -euo pipefail
: "${AWS_REGION:?Set AWS_REGION}"
: "${AWS_AZ:?Set AWS_AZ}"
: "${AMI_ID:?Set AMI_ID}"

pushd infra/aws-mac-runner >/dev/null
  terraform destroy -auto-approve -var "region=$AWS_REGION" -var "az=$AWS_AZ" -var "ami_id=$AMI_ID"
popd >/dev/null

echo "[✓] Destroy requested. Pamiętaj: Dedicated Host ma minimalny czas rozliczeniowy (24h)."
