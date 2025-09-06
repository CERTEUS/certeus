#!/bin/bash

# CERTEUS VS Code Autonomous Configuration Enforcer
# This script ensures VS Code operates in fully autonomous mode

echo "🔧 Enforcing VS Code Autonomous Configuration..."

# VS Code user settings path
VSCODE_USER_SETTINGS="$HOME/.vscode-server/data/User/settings.json"
VSCODE_LOCAL_SETTINGS="$HOME/.vscode/User/settings.json"

# Function to merge autonomous settings
merge_autonomous_settings() {
    local target_file="$1"
    local backup_file="${target_file}.backup.$(date +%s)"
    
    if [ -f "$target_file" ]; then
        echo "📄 Backing up existing settings: $backup_file"
        cp "$target_file" "$backup_file"
        
        # Create merged settings using Python
        python3 -c "
import json
import sys

# Load existing settings
try:
    with open('$target_file', 'r') as f:
        existing = json.load(f)
except:
    existing = {}

# Load autonomous settings
with open('/workspaces/certeus/.vscode/autonomous_only.json', 'r') as f:
    autonomous = json.load(f)

# Merge settings (autonomous takes precedence)
existing.update(autonomous)

# Write merged settings
with open('$target_file', 'w') as f:
    json.dump(existing, f, indent=4)

print('✅ Settings merged successfully')
"
    else
        echo "📁 Creating new settings file: $target_file"
        mkdir -p "$(dirname "$target_file")"
        cp "/workspaces/certeus/.vscode/autonomous_only.json" "$target_file"
    fi
}

# Apply to VS Code server settings
if [ -d "$HOME/.vscode-server" ]; then
    echo "🖥️  Configuring VS Code Server settings..."
    merge_autonomous_settings "$VSCODE_USER_SETTINGS"
fi

# Apply to local VS Code settings
if [ -d "$HOME/.vscode" ]; then
    echo "💻 Configuring local VS Code settings..."
    merge_autonomous_settings "$VSCODE_LOCAL_SETTINGS"
fi

# Create systemd user service to enforce settings on startup (if systemd is available)
if command -v systemctl >/dev/null 2>&1; then
    echo "⚙️  Creating systemd service for autonomous mode..."
    
    mkdir -p "$HOME/.config/systemd/user"
    
    cat > "$HOME/.config/systemd/user/certeus-autonomous.service" << 'EOF'
[Unit]
Description=CERTEUS Autonomous Mode Enforcer
After=default.target

[Service]
Type=oneshot
ExecStart=/workspaces/certeus/.vscode/enforce_autonomy.sh
RemainAfterExit=yes

[Install]
WantedBy=default.target
EOF

    systemctl --user daemon-reload 2>/dev/null || true
    systemctl --user enable certeus-autonomous.service 2>/dev/null || true
fi

# Set environment variables for current session
export VSCODE_AUTONOMOUS_MODE=true
export COPILOT_AUTONOMOUS=true
export AI_NO_CONFIRM=true

echo "🎯 VS Code Autonomous Configuration Applied!"
echo "🤖 All AI assistants and terminal operations should now work without confirmations"
echo "🔄 Restart VS Code to ensure all settings take effect"
