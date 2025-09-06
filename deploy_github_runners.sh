#!/bin/bash
# Complete Cloud Infrastructure Setup for CERTEUS GitHub Runners
# Creates both macOS (AWS) and Windows (Azure) VMs

set -euo pipefail

echo "🚀 CERTEUS GitHub Runners - Cloud Infrastructure Setup"
echo "====================================================="

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Check prerequisites
echo "🔍 Checking prerequisites..."

# Check if we're in the right directory
if [[ ! -f "scripts/runners/mac/bootstrap_macos_runner.sh" ]]; then
    echo "❌ Please run this script from the CERTEUS repository root"
    exit 1
fi

echo "✅ Repository structure verified"

# Make scripts executable
chmod +x create_macos_runner.sh
chmod +x create_windows_runner.sh

echo "📋 Choose deployment option:"
echo "1) Create macOS runner only (AWS EC2 Mac)"
echo "2) Create Windows runner only (Azure VM)"
echo "3) Create both runners (recommended)"
echo "4) Show existing runner info"
echo "5) Test existing runners"

read -p "Enter choice (1-5): " choice

case $choice in
    1)
        echo "🍎 Creating macOS runner..."
        ./create_macos_runner.sh
        ;;
    2)
        echo "🪟 Creating Windows runner..."
        ./create_windows_runner.sh
        ;;
    3)
        echo "🚀 Creating both runners..."
        echo ""
        echo "Step 1: Creating macOS runner (AWS)..."
        ./create_macos_runner.sh

        echo ""
        echo "Step 2: Creating Windows runner (Azure)..."
        ./create_windows_runner.sh

        echo ""
        echo "🎉 Both runners created!"
        echo "========================"
        cat macos-runner-info.txt
        echo ""
        cat windows-runner-info.txt
        ;;
    4)
        echo "📋 Existing runner information:"
        if [[ -f "macos-runner-info.txt" ]]; then
            echo ""
            echo "🍎 macOS Runner:"
            cat macos-runner-info.txt
        fi
        if [[ -f "windows-runner-info.txt" ]]; then
            echo ""
            echo "🪟 Windows Runner:"
            cat windows-runner-info.txt
        fi
        if [[ ! -f "macos-runner-info.txt" && ! -f "windows-runner-info.txt" ]]; then
            echo "❌ No runner info files found. Create runners first."
        fi
        ;;
    5)
        echo "🧪 Testing existing runners..."
        if command -v gh &> /dev/null; then
            echo "📋 Current GitHub runners:"
            gh api repos/CERTEUS/certeus/actions/runners --jq '.runners[] | {id,name,status,labels:[.labels[].name]}'

            echo ""
            echo "🚀 Running test workflow..."
            gh workflow run proofs-fs-selfhosted.yml -R CERTEUS/certeus -r main
            echo "✅ Test workflow triggered. Check GitHub Actions tab."
        else
            echo "❌ GitHub CLI not found. Install with: brew install gh (macOS) or apt install gh (Linux)"
        fi
        ;;
    *)
        echo "❌ Invalid choice"
        exit 1
        ;;
esac

echo ""
echo "📋 Next Steps After VM Creation:"
echo "================================"
echo ""
echo "🍎 macOS Runner Setup:"
echo "1. SSH to macOS instance using provided key"
echo "2. Run: ~/setup_runner.sh"
echo "3. Authenticate with GitHub when prompted"
echo "4. Approve macFUSE in System Settings > Privacy & Security"
echo "5. Restart if macOS prompts"
echo ""
echo "🪟 Windows Runner Setup:"
echo "1. RDP to Windows VM using provided credentials"
echo "2. Run PowerShell as Administrator"
echo "3. Execute: Desktop\\Setup-GitHub-Runner.ps1"
echo "4. Authenticate with GitHub when prompted"
echo "5. Reboot if Dokan installer requires it"
echo ""
echo "🔍 Verification:"
echo "• Check GitHub repo Settings > Actions > Runners"
echo "• Expect to see both runners with 'Online' status"
echo "• Labels: [self-hosted, macos, macfuse] and [self-hosted, windows, dokan]"
echo ""
echo "🧪 Testing:"
echo "• Run: gh workflow run proofs-fs-selfhosted.yml"
echo "• Monitor in GitHub Actions tab"
echo ""
echo "⚠️  Important Notes:"
echo "• macOS instances take 10-15 minutes to fully boot"
echo "• Windows VMs are ready for RDP in 2-3 minutes"
echo "• Both VMs will have auto-shutdown after 4 hours (cost optimization)"
echo "• Keep SSH keys and RDP credentials secure"

# Create summary file
cat > runners-deployment-summary.txt << EOF
CERTEUS GitHub Runners Deployment Summary
=========================================
Deployment Date: $(date)
Repository: CERTEUS/certeus

Infrastructure Created:
- macOS Runner: AWS EC2 Mac instance (mac2.metal)
- Windows Runner: Azure VM (Standard_D4s_v3)

Required Manual Steps:
1. SSH to macOS and run setup script
2. RDP to Windows and run setup script
3. Authenticate with GitHub on both
4. Approve macFUSE/Dokan installations
5. Restart VMs if prompted

Expected Outcome:
- Two online GitHub self-hosted runners
- Ready for ProofFS testing workflows
- Labels: [self-hosted, macos, macfuse], [self-hosted, windows, dokan]

Files Created:
- macos-runner-info.txt (connection details)
- windows-runner-info.txt (connection details)
- SSH key: certeus-mac-runner.pem

Next: Run ProofFS tests with self-hosted runners
EOF

echo "✅ Deployment summary saved to: runners-deployment-summary.txt"
