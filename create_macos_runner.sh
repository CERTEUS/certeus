#!/bin/bash
# AWS EC2 Mac Instance Creation for GitHub Self-Hosted Runner
# CERTEUS/certeus - macOS Runner with macFUSE

set -euo pipefail

echo "🍎 Creating AWS EC2 Mac Instance for GitHub Runner"
echo "=================================================="

# Configuration
INSTANCE_TYPE="mac2.metal"  # Dedicated Mac instance
AMI_ID="ami-0c2f4ac7dd9eb5ee3"  # macOS Ventura 13.6 (us-east-1)
KEY_NAME="certeus-mac-runner"
SECURITY_GROUP="certeus-runners-sg"
SUBNET_ID=""  # Will be auto-detected
REGION="us-east-1"

# Check AWS CLI
if ! command -v aws &> /dev/null; then
    echo "❌ AWS CLI not found. Installing..."
    if [[ "$OSTYPE" == "darwin"* ]]; then
        brew install awscli
    else
        curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip"
        unzip awscliv2.zip
        sudo ./aws/install
    fi
fi

# Verify AWS credentials
if ! aws sts get-caller-identity &> /dev/null; then
    echo "❌ AWS credentials not configured. Run: aws configure"
    exit 1
fi

echo "✅ AWS CLI configured"

# Create security group if not exists
if ! aws ec2 describe-security-groups --group-names "$SECURITY_GROUP" --region "$REGION" &> /dev/null; then
    echo "🔒 Creating security group..."
    VPC_ID=$(aws ec2 describe-vpcs --region "$REGION" --filters "Name=isDefault,Values=true" --query 'Vpcs[0].VpcId' --output text)

    aws ec2 create-security-group \
        --group-name "$SECURITY_GROUP" \
        --description "Security group for CERTEUS GitHub runners" \
        --vpc-id "$VPC_ID" \
        --region "$REGION"

    # Allow SSH (22) and GitHub Runner communication
    aws ec2 authorize-security-group-ingress \
        --group-name "$SECURITY_GROUP" \
        --protocol tcp \
        --port 22 \
        --cidr 0.0.0.0/0 \
        --region "$REGION"

    # Allow HTTPS outbound for GitHub API
    aws ec2 authorize-security-group-egress \
        --group-name "$SECURITY_GROUP" \
        --protocol tcp \
        --port 443 \
        --cidr 0.0.0.0/0 \
        --region "$REGION"

    echo "✅ Security group created"
else
    echo "✅ Security group exists"
fi

# Create key pair if not exists
if ! aws ec2 describe-key-pairs --key-names "$KEY_NAME" --region "$REGION" &> /dev/null; then
    echo "🔑 Creating key pair..."
    aws ec2 create-key-pair \
        --key-name "$KEY_NAME" \
        --region "$REGION" \
        --query 'KeyMaterial' \
        --output text > "${KEY_NAME}.pem"
    chmod 400 "${KEY_NAME}.pem"
    echo "✅ Key pair created: ${KEY_NAME}.pem"
else
    echo "✅ Key pair exists"
fi

# Get default subnet
if [ -z "$SUBNET_ID" ]; then
    SUBNET_ID=$(aws ec2 describe-subnets \
        --region "$REGION" \
        --filters "Name=default-for-az,Values=true" \
        --query 'Subnets[0].SubnetId' \
        --output text)
fi

# Create user data script for auto-setup
cat > mac-userdata.sh << 'EOF'
#!/bin/bash
# Auto-setup script for macOS EC2 instance

# Install Homebrew if not present
if ! command -v brew &> /dev/null; then
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    echo 'eval "$(/opt/homebrew/bin/brew shellenv)"' >> ~/.zprofile
    eval "$(/opt/homebrew/bin/brew shellenv)"
fi

# Install GitHub CLI
brew install gh

# Clone the repository (will need manual gh auth login)
echo "Repository ready for setup. Run these commands after SSH:"
echo "1. gh auth login --hostname github.com --web --git-protocol https"
echo "2. git clone https://github.com/CERTEUS/certeus.git"
echo "3. cd certeus"
echo "4. REPO_SLUG=CERTEUS/certeus bash scripts/runners/mac/bootstrap_macos_runner.sh"

# Create setup reminder
cat > ~/setup_runner.sh << 'SETUP'
#!/bin/bash
echo "🍎 macOS GitHub Runner Setup"
echo "1. Authenticate with GitHub:"
gh auth login --hostname github.com --web --git-protocol https

echo "2. Clone repository:"
git clone https://github.com/CERTEUS/certeus.git
cd certeus

echo "3. Run bootstrap script:"
REPO_SLUG=CERTEUS/certeus bash scripts/runners/mac/bootstrap_macos_runner.sh

echo "4. After macFUSE installation, approve in System Settings > Privacy & Security"
echo "5. Restart if prompted"
SETUP

chmod +x ~/setup_runner.sh
echo "Setup script created at ~/setup_runner.sh"
EOF

# Launch EC2 Mac instance
echo "🚀 Launching EC2 Mac instance..."
INSTANCE_ID=$(aws ec2 run-instances \
    --image-id "$AMI_ID" \
    --count 1 \
    --instance-type "$INSTANCE_TYPE" \
    --key-name "$KEY_NAME" \
    --security-groups "$SECURITY_GROUP" \
    --subnet-id "$SUBNET_ID" \
    --user-data file://mac-userdata.sh \
    --tag-specifications 'ResourceType=instance,Tags=[{Key=Name,Value=certeus-macos-runner},{Key=Project,Value=CERTEUS},{Key=Purpose,Value=GitHub-Runner}]' \
    --region "$REGION" \
    --query 'Instances[0].InstanceId' \
    --output text)

echo "✅ Instance launched: $INSTANCE_ID"

# Wait for instance to be running
echo "⏳ Waiting for instance to be running..."
aws ec2 wait instance-running --instance-ids "$INSTANCE_ID" --region "$REGION"

# Get public IP
PUBLIC_IP=$(aws ec2 describe-instances \
    --instance-ids "$INSTANCE_ID" \
    --region "$REGION" \
    --query 'Reservations[0].Instances[0].PublicIpAddress' \
    --output text)

echo "🎉 macOS EC2 Instance Ready!"
echo "================================"
echo "Instance ID: $INSTANCE_ID"
echo "Public IP: $PUBLIC_IP"
echo "SSH Key: ${KEY_NAME}.pem"
echo ""
echo "📋 Next Steps:"
echo "1. SSH to instance: ssh -i ${KEY_NAME}.pem ec2-user@${PUBLIC_IP}"
echo "2. Run setup script: ~/setup_runner.sh"
echo "3. Follow the prompts to authenticate and install runner"
echo ""
echo "⚠️  Note: Mac instances take 10-15 minutes to fully boot"

# Save connection info
cat > macos-runner-info.txt << EOF
macOS Runner Instance Information
=================================
Instance ID: $INSTANCE_ID
Public IP: $PUBLIC_IP
SSH Command: ssh -i ${KEY_NAME}.pem ec2-user@${PUBLIC_IP}
Region: $REGION
Instance Type: $INSTANCE_TYPE

Setup Commands (run on instance):
1. ~/setup_runner.sh
2. Follow GitHub authentication prompts
3. Approve macFUSE in System Settings if prompted
4. Restart if macOS requests it

Expected Runner Labels: self-hosted, macos, macfuse
EOF

echo "✅ Instance info saved to: macos-runner-info.txt"
