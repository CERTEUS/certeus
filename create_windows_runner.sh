#!/bin/bash
# Azure Windows VM Creation for GitHub Self-Hosted Runner
# CERTEUS/certeus - Windows Runner with Dokan

set -euo pipefail

echo "🪟 Creating Azure Windows VM for GitHub Runner"
echo "=============================================="

# Configuration
RESOURCE_GROUP="certeus-runners-rg"
VM_NAME="certeus-windows-runner"
LOCATION="eastus"
VM_SIZE="Standard_D4s_v3"  # 4 vCPUs, 16GB RAM
IMAGE="Win2022Datacenter"
ADMIN_USERNAME="certeus"
ADMIN_PASSWORD="CerteusRunner2025!"

# Check Azure CLI
if ! command -v az &> /dev/null; then
    echo "❌ Azure CLI not found. Installing..."
    if [[ "$OSTYPE" == "darwin"* ]]; then
        brew install azure-cli
    else
        curl -sL https://aka.ms/InstallAzureCLIDeb | sudo bash
    fi
fi

# Check if logged in
if ! az account show &> /dev/null; then
    echo "❌ Not logged into Azure. Run: az login"
    exit 1
fi

echo "✅ Azure CLI configured"

# Create resource group
if ! az group show --name "$RESOURCE_GROUP" &> /dev/null; then
    echo "📁 Creating resource group..."
    az group create \
        --name "$RESOURCE_GROUP" \
        --location "$LOCATION"
    echo "✅ Resource group created"
else
    echo "✅ Resource group exists"
fi

# Create network security group
NSG_NAME="${VM_NAME}-nsg"
if ! az network nsg show --resource-group "$RESOURCE_GROUP" --name "$NSG_NAME" &> /dev/null; then
    echo "🔒 Creating network security group..."
    az network nsg create \
        --resource-group "$RESOURCE_GROUP" \
        --name "$NSG_NAME"

    # Allow RDP
    az network nsg rule create \
        --resource-group "$RESOURCE_GROUP" \
        --nsg-name "$NSG_NAME" \
        --name "AllowRDP" \
        --protocol tcp \
        --priority 1001 \
        --destination-port-range 3389 \
        --access allow

    echo "✅ Network security group created"
else
    echo "✅ Network security group exists"
fi

# Create custom script for Windows setup
cat > windows-setup.ps1 << 'EOF'
# Windows PowerShell Setup Script for GitHub Runner
Write-Host "🪟 Setting up Windows for GitHub Runner..." -ForegroundColor Green

# Install Chocolatey
if (-not (Get-Command choco -ErrorAction SilentlyContinue)) {
    Write-Host "📦 Installing Chocolatey..." -ForegroundColor Yellow
    Set-ExecutionPolicy Bypass -Scope Process -Force
    [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
    Invoke-Expression ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))
}

# Install GitHub CLI
if (-not (Get-Command gh -ErrorAction SilentlyContinue)) {
    Write-Host "📦 Installing GitHub CLI..." -ForegroundColor Yellow
    winget install --id GitHub.cli -e -h
}

# Install Git if not present
if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
    Write-Host "📦 Installing Git..." -ForegroundColor Yellow
    winget install --id Git.Git -e -h
}

# Create setup script on desktop
$SetupScript = @"
# GitHub Runner Setup Script
Write-Host "🚀 CERTEUS Windows Runner Setup" -ForegroundColor Green
Write-Host "================================" -ForegroundColor Green

Write-Host "1. Authenticate with GitHub:" -ForegroundColor Yellow
gh auth login --hostname github.com --web --git-protocol https

Write-Host "2. Clone repository:" -ForegroundColor Yellow
Set-Location C:\
git clone https://github.com/CERTEUS/certeus.git
Set-Location C:\certeus

Write-Host "3. Set execution policy:" -ForegroundColor Yellow
Set-ExecutionPolicy Bypass -Scope Process -Force

Write-Host "4. Run bootstrap script:" -ForegroundColor Yellow
powershell -File scripts/runners/windows/bootstrap_windows_runner.ps1 -RepoSlug 'CERTEUS/certeus'

Write-Host "5. Reboot if Dokan installation requires it" -ForegroundColor Yellow
Write-Host "Setup complete! Check GitHub repository for runner status." -ForegroundColor Green
"@

$SetupScript | Out-File -FilePath "C:\Users\$env:USERNAME\Desktop\Setup-GitHub-Runner.ps1" -Encoding UTF8

Write-Host "✅ Setup script created on Desktop" -ForegroundColor Green
Write-Host "📋 After VM starts, run Setup-GitHub-Runner.ps1 from Desktop" -ForegroundColor Cyan
EOF

# Create the VM
echo "🚀 Creating Windows VM..."
az vm create \
    --resource-group "$RESOURCE_GROUP" \
    --name "$VM_NAME" \
    --image "$IMAGE" \
    --size "$VM_SIZE" \
    --admin-username "$ADMIN_USERNAME" \
    --admin-password "$ADMIN_PASSWORD" \
    --nsg "$NSG_NAME" \
    --public-ip-sku Standard \
    --storage-sku Premium_LRS \
    --os-disk-size-gb 128 \
    --tags Project=CERTEUS Purpose=GitHub-Runner OS=Windows

echo "✅ VM created successfully"

# Get VM information
VM_INFO=$(az vm show \
    --resource-group "$RESOURCE_GROUP" \
    --name "$VM_NAME" \
    --show-details \
    --query '{name:name, resourceGroup:resourceGroup, location:location, vmSize:hardwareProfile.vmSize, publicIp:publicIps, privateIp:privateIps}' \
    --output json)

PUBLIC_IP=$(echo "$VM_INFO" | jq -r '.publicIp')
PRIVATE_IP=$(echo "$VM_INFO" | jq -r '.privateIp')

# Upload setup script to VM
echo "📤 Uploading setup script to VM..."
az vm run-command invoke \
    --resource-group "$RESOURCE_GROUP" \
    --name "$VM_NAME" \
    --command-id RunPowerShellScript \
    --scripts @windows-setup.ps1

echo "🎉 Windows VM Ready!"
echo "==================="
echo "VM Name: $VM_NAME"
echo "Public IP: $PUBLIC_IP"
echo "Private IP: $PRIVATE_IP"
echo "Username: $ADMIN_USERNAME"
echo "Password: $ADMIN_PASSWORD"
echo ""
echo "📋 Next Steps:"
echo "1. RDP to VM: mstsc /v:$PUBLIC_IP"
echo "2. Login with username: $ADMIN_USERNAME"
echo "3. Run Desktop\\Setup-GitHub-Runner.ps1 in PowerShell (Admin)"
echo "4. Follow GitHub authentication prompts"
echo "5. Reboot if Dokan installation requires it"

# Save connection info
cat > windows-runner-info.txt << EOF
Windows Runner VM Information
============================
VM Name: $VM_NAME
Resource Group: $RESOURCE_GROUP
Public IP: $PUBLIC_IP
Private IP: $PRIVATE_IP
Location: $LOCATION
VM Size: $VM_SIZE

Credentials:
Username: $ADMIN_USERNAME
Password: $ADMIN_PASSWORD

RDP Connection: mstsc /v:$PUBLIC_IP

Setup Steps:
1. RDP to the VM
2. Run PowerShell as Administrator
3. Execute: C:\\Users\\$ADMIN_USERNAME\\Desktop\\Setup-GitHub-Runner.ps1
4. Follow GitHub auth prompts
5. Reboot if prompted by Dokan installer

Expected Runner Labels: self-hosted, windows, dokan
EOF

echo "✅ VM info saved to: windows-runner-info.txt"
echo ""
echo "⏳ VM is starting up... RDP will be available in 2-3 minutes"
