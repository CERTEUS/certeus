# ============================================================================
#  CODESPACES macOS RUNNER PACK  |  ForgeHeader v1
#  PL: Zestaw do postawienia self-hosted runnera macOS z poziomu Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, rejestracja runnera przez GH API.
#  EN: End-to-end self-hosted macOS runner from Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, runner registration via GH API.
#
#  File      : infra/aws-mac-runner/variables.tf
#  Author    : Radosław Skarżycki (Radziu)
#  Version   : 0.2.0
#  Date (UTC): 2025-09-06T17:40:49Z
#  License   : MIT
#  Repo      : <fill-after-commit>
# ============================================================================

variable "region" {
  type        = string
  description = "AWS region (must support EC2 Mac)"
}

variable "az" {
  type        = string
  description = "Availability Zone (must have mac1.metal capacity)"
}

variable "ami_id" {
  type        = string
  description = "macOS AMI ID (see scripts/aws-find-macos-ami.sh)"
}

variable "instance_name" {
  type        = string
  default     = "mac-runner-1"
  description = "Name tag for the macOS instance"
}

variable "root_volume_size_gb" {
  type        = number
  default     = 200
  description = "Root EBS size in GiB"
}
