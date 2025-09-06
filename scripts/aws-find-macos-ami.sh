# ============================================================================
#  CODESPACES macOS RUNNER PACK  |  ForgeHeader v1
#  PL: Zestaw do postawienia self-hosted runnera macOS z poziomu Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, rejestracja runnera przez GH API.
#  EN: End-to-end self-hosted macOS runner from Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, runner registration via GH API.
#
#  File      : scripts/aws-find-macos-ami.sh
#  Author    : Radosław Skarżycki (Radziu)
#  Version   : 0.2.0
#  Date (UTC): 2025-09-06T17:40:49Z
#  License   : MIT
#  Repo      : <fill-after-commit>
# ============================================================================

#!/usr/bin/env bash
set -euo pipefail
: "${AWS_REGION:?Set AWS_REGION}"

# Lists recent official macOS AMIs from AWS in the region.
aws ec2 describe-images   --owners amazon   --filters "Name=platform,Values=macOS"   --query "Images[].{ImageId:ImageId,Name:Name,CreationDate:CreationDate}"   --region "$AWS_REGION"   | jq -r '.[] | [.CreationDate, .ImageId, .Name] | @tsv'   | sort -r
