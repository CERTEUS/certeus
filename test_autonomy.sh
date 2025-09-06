#!/bin/bash

# CERTEUS Autonomous Terminal Test
# This script tests if all terminal operations work without manual confirmations

echo "🧪 Testing CERTEUS Autonomous Terminal Operations..."
echo "=" | tr '=' '-' | head -c 60; echo

# Test 1: Git operations
echo "Test 1: Git Status (should work without prompts)"
git status --porcelain >/dev/null 2>&1 && echo "✅ Git status - OK" || echo "❌ Git status - FAILED"

# Test 2: Environment variables
echo "Test 2: Autonomous environment variables"
[ "$CERTEUS_AUTONOMOUS_MODE" = "true" ] && echo "✅ CERTEUS_AUTONOMOUS_MODE - OK" || echo "❌ CERTEUS_AUTONOMOUS_MODE - FAILED"
[ "$NO_CONFIRM" = "true" ] && echo "✅ NO_CONFIRM - OK" || echo "❌ NO_CONFIRM - FAILED" 
[ "$DEBIAN_FRONTEND" = "noninteractive" ] && echo "✅ DEBIAN_FRONTEND - OK" || echo "❌ DEBIAN_FRONTEND - FAILED"
[ "$GIT_TERMINAL_PROMPT" = "0" ] && echo "✅ GIT_TERMINAL_PROMPT - OK" || echo "❌ GIT_TERMINAL_PROMPT - FAILED"

# Test 3: Python operations
echo "Test 3: Python environment"
python3 --version >/dev/null 2>&1 && echo "✅ Python3 available - OK" || echo "❌ Python3 - FAILED"
[ "$PYTHONUNBUFFERED" = "1" ] && echo "✅ PYTHONUNBUFFERED - OK" || echo "❌ PYTHONUNBUFFERED - FAILED"

# Test 4: File operations
echo "Test 4: File system operations"
touch /tmp/certeus_test_file 2>/dev/null && rm -f /tmp/certeus_test_file 2>/dev/null && echo "✅ File operations - OK" || echo "❌ File operations - FAILED"

# Test 5: VS Code settings check
echo "Test 5: VS Code autonomous settings"
if [ -f "/workspaces/certeus/.vscode/settings.json" ]; then
    grep -q "requireManualApproval.*false" /workspaces/certeus/.vscode/settings.json && echo "✅ VS Code autonomous settings - OK" || echo "❌ VS Code autonomous settings - FAILED"
else
    echo "❌ VS Code settings file not found"
fi

echo
echo "🎯 Autonomous Terminal Test Complete!"
echo "🤖 If all tests show ✅, terminal should operate without manual confirmations"
