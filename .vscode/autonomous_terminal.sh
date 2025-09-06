#!/bin/bash

# CERTEUS AUTONOMOUS TERMINAL CONFIGURATION
# This script ensures zero prompts and confirmations in terminal operations

export CERTEUS_AUTONOMOUS_MODE=true
export NO_CONFIRM=true
export FORCE_YES=true
export DEBIAN_FRONTEND=noninteractive
export GIT_TERMINAL_PROMPT=0
export GIT_ASKPASS=/bin/echo

# Disable all interactive prompts
export PYTHONUNBUFFERED=1
export PYTHONDONTWRITEBYTECODE=1
export PIP_DISABLE_PIP_VERSION_CHECK=1
export PIP_NO_INPUT=1
export PIP_QUIET=1

# Git automation settings
git config --global advice.addIgnoredFile false
git config --global advice.addEmptyPathspec false
git config --global advice.pushUpdateRejected false
git config --global advice.pushNonFFCurrent false
git config --global advice.pushNonFFMatching false
git config --global advice.pushAlreadyExists false
git config --global advice.pushFetchFirst false
git config --global advice.pushNeedsForce false
git config --global advice.statusHints false
git config --global advice.statusUoption false
git config --global advice.commitBeforeMerge false
git config --global advice.resolveConflict false
git config --global advice.implicitIdentity false
git config --global advice.detachedHead false
git config --global advice.amWorkDir false
git config --global advice.rmHints false
git config --global advice.addEmbeddedRepo false

# Disable all Git prompts
git config --global core.askpass ""
git config --global core.editor /bin/true
git config --global merge.tool /bin/true
git config --global diff.tool /bin/true

# NPM automation settings (if needed)
npm config set audit false 2>/dev/null || true
npm config set fund false 2>/dev/null || true
npm config set update-notifier false 2>/dev/null || true

# Apt automation settings (if needed)
echo 'APT::Get::Assume-Yes "true";' | sudo tee -a /etc/apt/apt.conf.d/90auto-yes >/dev/null 2>&1 || true
echo 'APT::Get::force-yes "true";' | sudo tee -a /etc/apt/apt.conf.d/90auto-yes >/dev/null 2>&1 || true
echo 'Dpkg::Options "--force-confdef";' | sudo tee -a /etc/apt/apt.conf.d/90auto-yes >/dev/null 2>&1 || true
echo 'Dpkg::Options "--force-confold";' | sudo tee -a /etc/apt/apt.conf.d/90auto-yes >/dev/null 2>&1 || true

# Make bash commands non-interactive by default
alias apt='apt -y'
alias apt-get='apt-get -y'
alias pip='pip --quiet --no-input'
alias pip3='pip3 --quiet --no-input'

echo "✅ CERTEUS Autonomous Terminal Configuration Applied"
echo "🤖 Terminal operates in zero-confirmation mode"
