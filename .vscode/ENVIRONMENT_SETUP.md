# ============================================================================
# CERTEUS - Cross-Platform Development Environment Setup
# ============================================================================
# PL: Konfiguracja środowiska deweloperskiego dla wszystkich platform
# EN: Development environment configuration for all platforms
# ============================================================================

# === SYSTEM REQUIREMENTS ===
minimum_requirements:
  ram: "4GB (8GB recommended)"
  storage: "2GB free space"
  python: "3.11+"
  git: "2.30+"
  node: "18+ (optional, for web clients)"

# === PLATFORM COMPATIBILITY ===
supported_platforms:
  desktop:
    - "Windows 10/11 (x64, ARM64)"
    - "macOS 12+ (Intel, Apple Silicon)"
    - "Linux Ubuntu 20.04+ / Debian 11+"
  mobile:
    - "Android 8+ (VS Code Mobile)"
    - "iOS 14+ (via GitHub Codespaces)"
  cloud:
    - "GitHub Codespaces"
    - "GitPod"
    - "Replit"
    - "CodeSandbox"

# === QUICK SETUP COMMANDS ===
setup_commands:
  windows: |
    # Install via winget
    winget install Microsoft.VisualStudioCode
    winget install Python.Python.3.11
    winget install Git.Git

    # Clone and setup
    git clone https://github.com/CERTEUS/certeus.git
    cd certeus
    python -m venv .venv
    .venv\Scripts\activate
    pip install -r requirements.txt
    code .

  macos: |
    # Install via Homebrew
    brew install --cask visual-studio-code
    brew install python@3.11 git

    # Clone and setup
    git clone https://github.com/CERTEUS/certeus.git
    cd certeus
    python3.11 -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    code .

  linux: |
    # Install via package manager (Ubuntu/Debian)
    sudo apt update
    sudo apt install -y python3.11 python3.11-venv python3-pip git

    # Install VS Code
    wget -qO- https://packages.microsoft.com/keys/microsoft.asc | gpg --dearmor > packages.microsoft.gpg
    sudo install -o root -g root -m 644 packages.microsoft.gpg /etc/apt/trusted.gpg.d/
    sudo sh -c 'echo "deb [arch=amd64,arm64,armhf signed-by=/etc/apt/trusted.gpg.d/packages.microsoft.gpg] https://packages.microsoft.com/repos/code stable main" > /etc/apt/sources.list.d/vscode.list'
    sudo apt install code

    # Clone and setup
    git clone https://github.com/CERTEUS/certeus.git
    cd certeus
    python3.11 -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    code .

  codespaces: |
    # Auto-configured via .devcontainer/
    # Just open in GitHub Codespaces
    # Environment ready in 2-3 minutes

# === MOBILE OPTIMIZATION ===
mobile_settings:
  touch_friendly:
    - "Large touch targets (44px minimum)"
    - "Swipe gestures enabled"
    - "Voice input support"

  performance:
    - "Reduced animations"
    - "Limited extensions"
    - "Optimized font sizes"

  connectivity:
    - "Offline mode support"
    - "Low bandwidth optimization"
    - "Auto-sync when online"

# === AUTOMATION FEATURES ===
automation:
  code_quality:
    - "Auto-format on save (Black)"
    - "Auto-lint (Ruff)"
    - "Auto-import sorting (isort)"
    - "Spell checking"

  testing:
    - "Auto-run tests on change"
    - "Coverage reporting"
    - "Performance benchmarks"

  deployment:
    - "Auto-build on push"
    - "Continuous integration"
    - "Security scanning"

# === PERFORMANCE OPTIMIZATIONS ===
performance:
  vs_code:
    - "Limited to 24 analyzed files"
    - "Disabled heavy type checking"
    - "Optimized search patterns"
    - "Memory usage monitoring"

  python:
    - "Virtual environment isolation"
    - "Dependency caching"
    - "Precompiled bytecode"
    - "Import optimization"

  network:
    - "Git LFS for large files"
    - "Compressed transfers"
    - "Delta sync"
    - "CDN acceleration"

# === TROUBLESHOOTING ===
common_issues:
  "Pylance slow":
    solution: "Already optimized - only 24 files analyzed"
    config: "pyrightconfig.json"

  "Memory usage high":
    solution: "Extensions automatically limited"
    config: ".vscode/settings.json"

  "Mobile lag":
    solution: "Touch-optimized settings active"
    config: "Responsive UI enabled"

  "Network issues":
    solution: "Offline mode + sync on reconnect"
    config: "Auto-retry enabled"

# === ENVIRONMENT VALIDATION ===
health_check:
  commands: |
    # Run these to verify setup
    python --version          # Should show 3.11+
    pip list | grep ruff      # Should show ruff installed
    code --version           # Should show VS Code version
    git status              # Should show clean repo

  expected_output: |
    ✅ Python 3.11.x
    ✅ Ruff linter installed
    ✅ VS Code running
    ✅ Git repository clean
    ✅ Pylance analyzing 24 files
    ✅ 0 errors reported

# === BACKUP & SYNC ===
data_management:
  auto_backup:
    - "Settings sync via GitHub"
    - "Extensions sync"
    - "Workspace preferences"

  version_control:
    - "All configs in git"
    - "Cross-device consistency"
    - "Rollback capability"
