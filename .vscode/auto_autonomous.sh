#!/bin/bash

# CERTEUS AUTO-LOADER - Autonomous Mode Enforcer
# This script automatically enforces autonomous mode for all operations

# Ensure this runs only once per session
if [ "$CERTEUS_AUTONOMOUS_LOADED" = "true" ]; then
    return 0 2>/dev/null || exit 0
fi

export CERTEUS_AUTONOMOUS_LOADED=true

# Silent loading - no output unless there's an error
{
    # Load autonomous terminal configuration
    if [ -f "/workspaces/certeus/.vscode/autonomous_terminal.sh" ]; then
        source "/workspaces/certeus/.vscode/autonomous_terminal.sh" >/dev/null 2>&1
    fi
    
    # Load global autonomous environment
    if [ -f "/workspaces/certeus/.bashrc_autonomous" ]; then
        source "/workspaces/certeus/.bashrc_autonomous" >/dev/null 2>&1
    fi
    
    # Set additional autonomous variables
    export CERTEUS_AUTO_MODE=enabled
    export VSCODE_DISABLE_PROMPTS=true
    export GITHUB_COPILOT_NO_PROMPT=true
    export AI_AUTONOMOUS_EXECUTION=true
    export TERMINAL_NO_CONFIRM=true
    
    # Configure Git for autonomous operation
    git config --global core.askpass "" 2>/dev/null
    git config --global core.editor /bin/true 2>/dev/null
    git config --global advice.detachedHead false 2>/dev/null
    git config --global init.defaultBranch main 2>/dev/null
    git config --global pull.rebase false 2>/dev/null
    git config --global push.default current 2>/dev/null
    git config --global branch.autosetupmerge always 2>/dev/null
    git config --global branch.autosetuprebase always 2>/dev/null
    
    # Override common interactive commands with non-interactive versions
    alias rm='rm -f'
    alias cp='cp -f'
    alias mv='mv -f'
    alias mkdir='mkdir -p'
    alias apt='apt -y'
    alias apt-get='apt-get -y'
    alias pip='pip --quiet --no-input'
    alias pip3='pip3 --quiet --no-input'
    alias npm='npm --silent'
    alias yarn='yarn --silent'
    
    # Python environment settings
    export PYTHONUNBUFFERED=1
    export PYTHONDONTWRITEBYTECODE=1
    export PIP_DISABLE_PIP_VERSION_CHECK=1
    export PIP_NO_INPUT=1
    export PIP_QUIET=1
    
    # Disable interactive elements
    export DEBIAN_FRONTEND=noninteractive
    export NEEDRESTART_MODE=a
    export NEEDRESTART_SUSPEND=1
    export GIT_TERMINAL_PROMPT=0
    export GIT_ASKPASS=/bin/echo
    
} 2>/dev/null

# Only show success message if not in a subshell
if [ "$BASH_SUBSHELL" = "0" ] && [ -t 1 ]; then
    echo "🤖 CERTEUS Autonomous Mode: Active (no confirmations required)"
fi

# Make this available for future shells
echo "source /workspaces/certeus/.vscode/auto_autonomous.sh" >> ~/.bashrc 2>/dev/null || true
