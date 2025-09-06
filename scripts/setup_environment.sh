#!/usr/bin/env bash
# ============================================================================
# CERTEUS - Universal Environment Setup Script
# ============================================================================
# PL: Uniwersalny skrypt konfiguracji środowiska
# EN: Universal environment setup script
# ============================================================================

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Detect OS
detect_os() {
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        echo "linux"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        echo "macos"
    elif [[ "$OSTYPE" == "cygwin" ]] || [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "win32" ]]; then
        echo "windows"
    else
        echo "unknown"
    fi
}

# Log functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check prerequisites
check_prerequisites() {
    log_info "Checking prerequisites..."

    # Python 3.11+
    if command -v python3 &> /dev/null; then
        PYTHON_VERSION=$(python3 --version | cut -d' ' -f2)
        log_success "Python $PYTHON_VERSION found"
    else
        log_error "Python 3.11+ required"
        return 1
    fi

    # Git
    if command -v git &> /dev/null; then
        GIT_VERSION=$(git --version | cut -d' ' -f3)
        log_success "Git $GIT_VERSION found"
    else
        log_error "Git required"
        return 1
    fi

    # VS Code (optional)
    if command -v code &> /dev/null; then
        CODE_VERSION=$(code --version | head -n1)
        log_success "VS Code $CODE_VERSION found"
    else
        log_warning "VS Code not found - install for best experience"
    fi
}

# Setup Python environment
setup_python_env() {
    log_info "Setting up Python environment..."

    # Create virtual environment
    if [[ ! -d ".venv" ]]; then
        python3 -m venv .venv
        log_success "Virtual environment created"
    else
        log_info "Virtual environment already exists"
    fi

    # Activate based on OS
    OS=$(detect_os)
    if [[ "$OS" == "windows" ]]; then
        source .venv/Scripts/activate
    else
        source .venv/bin/activate
    fi

    # Upgrade pip
    pip install --upgrade pip

    # Install dependencies
    if [[ -f "requirements.txt" ]]; then
        pip install -r requirements.txt
        log_success "Dependencies installed"
    fi
}

# Configure VS Code
configure_vscode() {
    if command -v code &> /dev/null; then
        log_info "Configuring VS Code..."

        # Install essential extensions
        code --install-extension ms-python.python
        code --install-extension ms-python.vscode-pylance
        code --install-extension charliermarsh.ruff
        code --install-extension github.copilot

        log_success "VS Code extensions installed"
    fi
}

# Optimize for device type
optimize_for_device() {
    # Detect if running on mobile/low-resource device
    MEMORY_GB=$(free -g 2>/dev/null | awk '/^Mem:/{print $2}' || echo "8")

    if [[ "$MEMORY_GB" -lt 4 ]]; then
        log_info "Low memory device detected - applying optimizations"

        # Create mobile-optimized settings
        mkdir -p .vscode
        cat > .vscode/mobile-settings.json << 'EOF'
{
    "editor.fontSize": 16,
    "editor.lineHeight": 22,
    "workbench.editor.limit.value": 3,
    "python.analysis.userFileIndexingLimit": 50,
    "editor.minimap.enabled": false,
    "workbench.activityBar.location": "hidden",
    "editor.suggest.showWords": false
}
EOF
        log_success "Mobile optimizations applied"
    fi
}

# Run health check
health_check() {
    log_info "Running environment health check..."

    local errors=0

    # Check Python
    if python3 --version &> /dev/null; then
        log_success "✅ Python: $(python3 --version)"
    else
        log_error "❌ Python not working"
        ((errors++))
    fi

    # Check virtual environment
    if [[ -d ".venv" ]]; then
        log_success "✅ Virtual environment exists"
    else
        log_error "❌ Virtual environment missing"
        ((errors++))
    fi

    # Check Pylance config
    if [[ -f "pyrightconfig.json" ]]; then
        ANALYZED_FILES=$(grep -c '"[^"]*\.py"' pyrightconfig.json || echo "0")
        log_success "✅ Pylance config: $ANALYZED_FILES files analyzed"
    else
        log_warning "⚠️  Pylance config missing"
    fi

    # Check Git
    if git status &> /dev/null; then
        log_success "✅ Git repository initialized"
    else
        log_warning "⚠️  Not a Git repository"
    fi

    if [[ $errors -eq 0 ]]; then
        log_success "🎉 Environment setup completed successfully!"
        log_info "Run 'source .venv/bin/activate' to start developing"
    else
        log_error "❌ Setup completed with $errors errors"
        return 1
    fi
}

# Main execution
main() {
    echo "============================================================================"
    echo "🚀 CERTEUS - Universal Environment Setup"
    echo "============================================================================"

    check_prerequisites || exit 1
    setup_python_env
    configure_vscode
    optimize_for_device
    health_check

    echo ""
    echo "🎯 Next steps:"
    echo "   1. Open VS Code: code ."
    echo "   2. Install recommended extensions"
    echo "   3. Start coding!"
}

# Run if called directly
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
