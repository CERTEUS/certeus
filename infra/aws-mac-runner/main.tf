# ============================================================================
#  CODESPACES macOS RUNNER PACK  |  ForgeHeader v1
#  PL: Zestaw do postawienia self-hosted runnera macOS z poziomu Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, rejestracja runnera przez GH API.
#  EN: End-to-end self-hosted macOS runner from Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, runner registration via GH API.
#
#  File      : infra/aws-mac-runner/main.tf
#  Author    : Radosław Skarżycki (Radziu)
#  Version   : 0.2.0
#  Date (UTC): 2025-09-06T17:40:49Z
#  License   : MIT
#  Repo      : <fill-after-commit>
# ============================================================================

terraform {
  required_version = ">= 1.5.0"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = ">= 5.0"
    }
  }
}

provider "aws" {
  region = var.region
}

# Domyślny VPC i domyślna podsieć w zadanej AZ (provider >= v5)
# Zamiast przestarzałych data sources `aws_default_*` używamy filtrów.
data "aws_vpc" "default" {
  default = true
}

data "aws_subnet" "default_az" {
  availability_zone = var.az
  default_for_az    = true
}

# Dedicated Host for mac1.metal (one instance per host)
resource "aws_ec2_host" "mac_host" {
  instance_type     = "mac1.metal"
  availability_zone = var.az
  auto_placement    = "off"
  host_recovery     = "on"
  tags = {
    Name = "mac-runner-host"
  }
}

# IAM role for SSM
data "aws_iam_policy" "ssm_core" {
  arn = "arn:aws:iam::aws:policy/AmazonSSMManagedInstanceCore"
}

resource "aws_iam_role" "mac_role" {
  name               = "mac-runner-ssm-role"
  assume_role_policy = jsonencode({
    Version = "2012-10-17",
    Statement = [{
      Action = "sts:AssumeRole",
      Effect = "Allow",
      Principal = {
        Service = "ec2.amazonaws.com"
      }
    }]
  })
}

resource "aws_iam_role_policy_attachment" "mac_ssm_attach" {
  role       = aws_iam_role.mac_role.name
  policy_arn = data.aws_iam_policy.ssm_core.arn
}

resource "aws_iam_instance_profile" "mac_profile" {
  name = "mac-runner-instance-profile"
  role = aws_iam_role.mac_role.name
}

# Security Group (outbound only; SSM doesn't need inbound)
resource "aws_security_group" "mac_sg" {
  name        = "mac-runner-sg"
  description = "Outbound only; SSM for management"
  vpc_id      = data.aws_vpc.default.id
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
  tags = {
    Name = "mac-runner-sg"
  }
}

# macOS Instance on the dedicated host
resource "aws_instance" "mac" {
  ami                         = var.ami_id
  instance_type               = "mac1.metal"
  host_id                     = aws_ec2_host.mac_host.id
  subnet_id                   = data.aws_subnet.default_az.id
  iam_instance_profile        = aws_iam_instance_profile.mac_profile.name
  vpc_security_group_ids      = [aws_security_group.mac_sg.id]
  # Public IP ensures outbound internet in default VPC (for SSM/bootstrap)
  # If you use private subnets with NAT or VPC endpoints for SSM, you can set this to false.
  associate_public_ip_address = true

  root_block_device {
    volume_size = var.root_volume_size_gb
    volume_type = "gp3"
  }

  tags = {
    Name = var.instance_name
  }
}

output "instance_id" {
  value = aws_instance.mac.id
}

output "host_id" {
  value = aws_ec2_host.mac_host.id
}
