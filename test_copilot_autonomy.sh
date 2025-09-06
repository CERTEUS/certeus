#!/bin/bash

# CERTEUS COPILOT AUTONOMY TEST
# Test czy GitHub Copilot działa w pełni autonomicznie

echo "🤖 Testing GitHub Copilot Autonomous Mode..."
echo "=" | tr '=' '-' | head -c 50; echo

# Test 1: Sprawdź ustawienia Copilot w VS Code
echo "Test 1: Checking Copilot settings in VS Code"
if grep -q "github.copilot.enable" /workspaces/certeus/.vscode/settings.json; then
    echo "✅ Copilot enabled - OK"
else
    echo "❌ Copilot not enabled - FAILED"
fi

if grep -q "autonomousExecution.*true" /workspaces/certeus/.vscode/settings.json; then
    echo "✅ Autonomous execution enabled - OK"
else
    echo "❌ Autonomous execution not enabled - FAILED"
fi

if grep -q "requireManualApproval.*false" /workspaces/certeus/.vscode/settings.json; then
    echo "✅ Manual approval disabled - OK"
else
    echo "❌ Manual approval not disabled - FAILED"
fi

if grep -q "requireConfirmation.*false" /workspaces/certeus/.vscode/settings.json; then
    echo "✅ Confirmation requirement disabled - OK"
else
    echo "❌ Confirmation requirement not disabled - FAILED"
fi

# Test 2: Sprawdź ustawienia chat
echo ""
echo "Test 2: Checking Copilot Chat settings"
if grep -q "github.copilot.chat.autonomousMode.*true" /workspaces/certeus/.vscode/settings.json; then
    echo "✅ Chat autonomous mode enabled - OK"
else
    echo "❌ Chat autonomous mode not enabled - FAILED"
fi

if grep -q "chat.experimental.autoExecuteCommands.*true" /workspaces/certeus/.vscode/settings.json; then
    echo "✅ Auto-execute commands enabled - OK"
else
    echo "❌ Auto-execute commands not enabled - FAILED"
fi

# Test 3: Sprawdź zmienne środowiskowe
echo ""
echo "Test 3: Checking environment variables"
[ "$CERTEUS_AUTONOMOUS_MODE" = "true" ] && echo "✅ CERTEUS_AUTONOMOUS_MODE - OK" || echo "❌ CERTEUS_AUTONOMOUS_MODE - FAILED"
[ "$VSCODE_AUTONOMOUS_MODE" = "true" ] && echo "✅ VSCODE_AUTONOMOUS_MODE - OK" || echo "❌ VSCODE_AUTONOMOUS_MODE - FAILED"

# Test 4: Sprawdź flagi autonomiczne
echo ""
echo "Test 4: Checking autonomous flags"
if [ -f "/workspaces/certeus/.vscode/.autonomous_active" ]; then
    echo "✅ Autonomous mode flag file exists - OK"
    cat /workspaces/certeus/.vscode/.autonomous_active
else
    echo "❌ Autonomous mode flag file missing - FAILED"
fi

echo ""
echo "🎯 COPILOT AUTONOMY TEST COMPLETE!"
echo "🤖 If all tests show ✅, Copilot should work autonomously"
echo ""
echo "CURRENT COPILOT SETTINGS SUMMARY:"
echo "🔧 Autonomous Execution: $(grep -o 'autonomousExecution.*' /workspaces/certeus/.vscode/settings.json | head -1)"
echo "🔧 Manual Approval: $(grep -o 'requireManualApproval.*' /workspaces/certeus/.vscode/settings.json | head -1)"
echo "🔧 Chat Autonomous: $(grep -o 'github.copilot.chat.autonomousMode.*' /workspaces/certeus/.vscode/settings.json | head -1)"
echo "🔧 Auto Execute: $(grep -o 'chat.experimental.autoExecuteCommands.*' /workspaces/certeus/.vscode/settings.json | head -1)"
