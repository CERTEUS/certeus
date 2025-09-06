#!/bin/bash
# Test script for verifying GitHub self-hosted runners
# CERTEUS/certeus

set -euo pipefail

echo "🧪 CERTEUS Runners Verification & Testing"
echo "========================================"

# Check GitHub CLI
if ! command -v gh &> /dev/null; then
    echo "❌ GitHub CLI not found. Please install it first."
    exit 1
fi

# Check authentication
if ! gh auth status &> /dev/null; then
    echo "❌ Not authenticated with GitHub. Run: gh auth login"
    exit 1
fi

echo "✅ GitHub CLI authenticated"

# Function to check runner status
check_runners() {
    echo "📋 Current GitHub Runners Status:"
    echo "================================="

    RUNNERS_JSON=$(gh api repos/CERTEUS/certeus/actions/runners)

    # Check if we have any runners
    RUNNER_COUNT=$(echo "$RUNNERS_JSON" | jq '.total_count')
    echo "Total runners: $RUNNER_COUNT"

    if [[ "$RUNNER_COUNT" -eq 0 ]]; then
        echo "❌ No runners found"
        return 1
    fi

    # Show each runner
    echo "$RUNNERS_JSON" | jq -r '.runners[] | "• \(.name) - Status: \(.status) - OS: \(.os) - Labels: \([.labels[].name] | join(", "))"'

    # Check for our specific runners
    MACOS_RUNNER=$(echo "$RUNNERS_JSON" | jq '.runners[] | select(.labels[].name == "macfuse") | .name' | head -1)
    WINDOWS_RUNNER=$(echo "$RUNNERS_JSON" | jq '.runners[] | select(.labels[].name == "dokan") | .name' | head -1)

    echo ""
    if [[ -n "$MACOS_RUNNER" ]]; then
        echo "✅ macOS runner found: $MACOS_RUNNER"
    else
        echo "❌ macOS runner with 'macfuse' label not found"
    fi

    if [[ -n "$WINDOWS_RUNNER" ]]; then
        echo "✅ Windows runner found: $WINDOWS_RUNNER"
    else
        echo "❌ Windows runner with 'dokan' label not found"
    fi
}

# Function to run test workflow
run_test_workflow() {
    echo ""
    echo "🚀 Running ProofFS Self-Hosted Test Workflow"
    echo "============================================"

    # Trigger the workflow
    if gh workflow run proofs-fs-selfhosted.yml -R CERTEUS/certeus -r main; then
        echo "✅ Workflow triggered successfully"

        # Wait a moment and show recent runs
        sleep 5
        echo ""
        echo "📋 Recent workflow runs:"
        gh run list --workflow=proofs-fs-selfhosted.yml --limit 3

        # Get the latest run ID
        LATEST_RUN=$(gh run list --workflow=proofs-fs-selfhosted.yml --limit 1 --json databaseId --jq '.[0].databaseId')

        if [[ -n "$LATEST_RUN" ]]; then
            echo ""
            echo "🔍 Monitor this run: https://github.com/CERTEUS/certeus/actions/runs/$LATEST_RUN"
            echo "Or use: gh run watch $LATEST_RUN"
        fi
    else
        echo "❌ Failed to trigger workflow"
        return 1
    fi
}

# Function to check VM connectivity
check_vm_connectivity() {
    echo ""
    echo "🔗 Checking VM Connectivity"
    echo "=========================="

    if [[ -f "macos-runner-info.txt" ]]; then
        echo "🍎 macOS Runner Info:"
        MACOS_IP=$(grep "Public IP:" macos-runner-info.txt | cut -d: -f2 | tr -d ' ')
        echo "Public IP: $MACOS_IP"

        if [[ -n "$MACOS_IP" && "$MACOS_IP" != "null" ]]; then
            echo "Testing SSH connectivity..."
            if timeout 10 nc -z "$MACOS_IP" 22 2>/dev/null; then
                echo "✅ SSH port accessible"
            else
                echo "❌ SSH port not accessible (VM may still be starting)"
            fi
        fi
    fi

    if [[ -f "windows-runner-info.txt" ]]; then
        echo ""
        echo "🪟 Windows Runner Info:"
        WINDOWS_IP=$(grep "Public IP:" windows-runner-info.txt | cut -d: -f2 | tr -d ' ')
        echo "Public IP: $WINDOWS_IP"

        if [[ -n "$WINDOWS_IP" && "$WINDOWS_IP" != "null" ]]; then
            echo "Testing RDP connectivity..."
            if timeout 10 nc -z "$WINDOWS_IP" 3389 2>/dev/null; then
                echo "✅ RDP port accessible"
            else
                echo "❌ RDP port not accessible (VM may still be starting)"
            fi
        fi
    fi
}

# Function to show setup commands
show_setup_commands() {
    echo ""
    echo "📋 Manual Setup Commands"
    echo "======================="

    if [[ -f "macos-runner-info.txt" ]]; then
        echo ""
        echo "🍎 macOS Setup Commands:"
        SSH_KEY=$(grep "SSH Command:" macos-runner-info.txt | cut -d: -f2- | tr -d ' ')
        echo "1. $SSH_KEY"
        echo "2. ~/setup_runner.sh"
        echo "3. Follow GitHub auth prompts"
        echo "4. Approve macFUSE in System Settings"
        echo "5. Restart if prompted"
    fi

    if [[ -f "windows-runner-info.txt" ]]; then
        echo ""
        echo "🪟 Windows Setup Commands:"
        RDP_IP=$(grep "Public IP:" windows-runner-info.txt | cut -d: -f2 | tr -d ' ')
        USERNAME=$(grep "Username:" windows-runner-info.txt | cut -d: -f2 | tr -d ' ')
        echo "1. mstsc /v:$RDP_IP"
        echo "2. Login as: $USERNAME"
        echo "3. Run PowerShell as Admin"
        echo "4. Execute: Desktop\\Setup-GitHub-Runner.ps1"
        echo "5. Follow GitHub auth prompts"
        echo "6. Reboot if Dokan requires it"
    fi
}

# Main menu
echo "Choose verification option:"
echo "1) Check runner status"
echo "2) Run test workflow"
echo "3) Check VM connectivity"
echo "4) Show setup commands"
echo "5) Complete verification (all of above)"

read -p "Enter choice (1-5): " choice

case $choice in
    1)
        check_runners
        ;;
    2)
        run_test_workflow
        ;;
    3)
        check_vm_connectivity
        ;;
    4)
        show_setup_commands
        ;;
    5)
        echo "🔍 Running complete verification..."
        check_runners
        check_vm_connectivity
        show_setup_commands

        echo ""
        read -p "Run test workflow? (y/N): " run_test
        if [[ "$run_test" =~ ^[Yy]$ ]]; then
            run_test_workflow
        fi
        ;;
    *)
        echo "❌ Invalid choice"
        exit 1
        ;;
esac

echo ""
echo "✅ Verification complete!"
echo ""
echo "📚 Useful commands:"
echo "• Monitor workflows: gh run list"
echo "• Watch specific run: gh run watch <run-id>"
echo "• Check runners: gh api repos/CERTEUS/certeus/actions/runners"
echo "• Re-run this script: ./test_runners.sh"
