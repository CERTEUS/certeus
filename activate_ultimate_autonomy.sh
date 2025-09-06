#!/bin/bash

# CERTEUS ULTIMATE AUTONOMOUS ACTIVATOR
# This script merges the autonomous profile with VS Code settings

echo "🚀 ACTIVATING ULTIMATE AUTONOMOUS MODE..."

# Backup current settings
cp /workspaces/certeus/.vscode/settings.json /workspaces/certeus/.vscode/settings.json.backup.$(date +%s)

# Create a temporary Python script to merge JSON settings
cat > /tmp/merge_autonomous.py << 'EOF'
import json
import sys

def merge_settings():
    # Load current settings
    try:
        with open('/workspaces/certeus/.vscode/settings.json', 'r') as f:
            current = json.load(f)
    except:
        current = {}
    
    # Load autonomous profile
    try:
        with open('/workspaces/certeus/.vscode/autonomous_profile.json', 'r') as f:
            profile = json.load(f)
            autonomous_settings = profile.get('settings', {})
    except Exception as e:
        print(f"Error loading autonomous profile: {e}")
        sys.exit(1)
    
    # Merge settings - autonomous profile overrides everything
    current.update(autonomous_settings)
    
    # Add extra autonomous flags
    extra_autonomous = {
        "workbench.commandPalette.experimental.askCopilot": False,
        "workbench.commandPalette.preserveInput": False,
        "workbench.quickOpen.closeOnFocusLost": True,
        "workbench.quickOpen.preserveInput": False,
        "diffEditor.ignoreTrimWhitespace": False,
        "editor.acceptSuggestionOnCommitCharacter": True,
        "editor.acceptSuggestionOnEnter": "on",
        "editor.quickSuggestions": {
            "other": "on",
            "comments": "on", 
            "strings": "on"
        },
        "editor.suggestOnTriggerCharacters": True,
        "editor.wordBasedSuggestions": "allDocuments",
        "editor.parameterHints.enabled": True,
        "editor.inlineSuggest.enabled": True,
        "editor.suggest.preview": True,
        "terminal.integrated.confirmOnKeypress": False,
        "terminal.integrated.enableBell": False,
        "terminal.integrated.smoothScrolling": False,
        "scm.diffDecorations": "none",
        "scm.alwaysShowProviders": False,
        "scm.showActionButton": False,
        "search.smartCase": True,
        "search.globalFindClipboard": False,
        "breadcrumbs.enabled": False,
        "outline.showVariables": False,
        "outline.showFunctions": False,
        "outline.showClasses": False,
        "zenMode.hideActivityBar": True,
        "zenMode.hideStatusBar": True,
        "zenMode.hideTabs": True,
        "zenMode.hideLineNumbers": True,
        "zenMode.centerLayout": False,
        "files.hotExit": "off",
        "files.enableTrash": False,
        "editor.minimap.enabled": False,
        "editor.scrollbar.vertical": "hidden",
        "editor.scrollbar.horizontal": "hidden",
        "editor.overviewRulerBorder": False,
        "editor.hideCursorInOverviewRuler": True,
        "workbench.activityBar.location": "hidden",
        "workbench.statusBar.visible": False,
        "workbench.editor.showTabs": "none"
    }
    
    current.update(extra_autonomous)
    
    # Write merged settings
    with open('/workspaces/certeus/.vscode/settings.json', 'w') as f:
        json.dump(current, f, indent=4)
    
    print("✅ Autonomous settings merged successfully")
    print(f"📊 Total settings: {len(current)}")

if __name__ == "__main__":
    merge_settings()
EOF

# Run the merge script
python3 /tmp/merge_autonomous.py

# Apply additional environment settings
export VSCODE_AUTONOMOUS_MODE=true
export NO_CONFIRMATIONS=true
export AUTO_EXECUTE=true
export CERTEUS_ULTIMATE_AUTONOMY=true

# Update git settings for autonomous operations
git config --global --add safe.directory "*"
git config --global init.defaultBranch main
git config --global push.autoSetupRemote true
git config --global pull.rebase false
git config --global advice.detachedHead false

# Set bash to non-interactive mode for automation
echo 'export DEBIAN_FRONTEND=noninteractive' >> ~/.bashrc
echo 'export CERTEUS_AUTONOMOUS=true' >> ~/.bashrc
echo 'export NO_PROMPT=true' >> ~/.bashrc

# Create autonomous flag file for VS Code to detect
echo "AUTONOMOUS_MODE_ACTIVE=true" > /workspaces/certeus/.vscode/.autonomous_active
echo "LAST_ACTIVATED=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> /workspaces/certeus/.vscode/.autonomous_active

echo "🎯 ULTIMATE AUTONOMOUS MODE ACTIVATED!"
echo "🤖 VS Code should now operate with ZERO manual confirmations"
echo "⚡ All AI assistants are in autonomous execution mode"
echo "🔧 Terminal operations are non-interactive"
echo "📝 Git operations are fully automated"

# Clean up
rm -f /tmp/merge_autonomous.py

echo ""
echo "🔄 RESTART VS CODE to apply all changes!"
echo "💡 Use: Ctrl+Shift+P -> 'Developer: Reload Window'"
