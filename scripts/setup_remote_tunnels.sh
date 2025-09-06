#!/bin/bash
# ============================================================================
# CERTEUS - VS Code Remote Tunnels Setup
# ============================================================================
# PL: Skrypt konfiguracji VS Code Remote Tunnels
# EN: VS Code Remote Tunnels setup script
# ============================================================================

set -euo pipefail

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_success() { echo -e "${GREEN}[SUCCESS]${NC} $1"; }
log_warning() { echo -e "${YELLOW}[WARNING]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

echo "============================================================================"
echo "🚀 VS Code Remote Tunnels Setup for CERTEUS"
echo "============================================================================"

# Check if VS Code is available
if ! command -v code &> /dev/null; then
    log_error "VS Code not found. Please install VS Code first."
    exit 1
fi

VS_CODE_VERSION=$(code --version | head -n1)
log_info "VS Code version: $VS_CODE_VERSION"

# Check if tunnel command is available
if code tunnel --help &> /dev/null; then
    log_success "✅ VS Code Remote Tunnels supported"
else
    log_warning "VS Code tunnels not available in this version"
    log_info "Alternative: Use GitHub Codespaces or install code-server"

    # Offer code-server alternative
    read -p "Install code-server as alternative? (y/n): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        log_info "Installing code-server..."
        curl -fsSL https://code-server.dev/install.sh | sh
        log_success "code-server installed. Run: code-server --bind-addr 0.0.0.0:8080"
    fi
    exit 0
fi

# Setup tunnel
TUNNEL_NAME="${1:-certeus-dev-$(whoami)}"
log_info "Setting up tunnel: $TUNNEL_NAME"

# Install Remote Tunnels extension if not present
log_info "Installing VS Code Remote extensions..."
code --install-extension ms-vscode.remote-repositories
code --install-extension ms-vscode-remote.remote-ssh
code --install-extension github.codespaces

# Create tunnel service script
cat > start_tunnel.sh << 'EOF'
#!/bin/bash
# Auto-restart tunnel service

TUNNEL_NAME="${1:-certeus-dev}"
LOG_FILE="tunnel.log"

log_with_timestamp() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $1" | tee -a "$LOG_FILE"
}

start_tunnel() {
    log_with_timestamp "Starting VS Code tunnel: $TUNNEL_NAME"
    code tunnel --name "$TUNNEL_NAME" --accept-server-license-terms 2>&1 | tee -a "$LOG_FILE"
}

# Main loop with auto-restart
while true; do
    start_tunnel
    exit_code=$?

    if [ $exit_code -eq 0 ]; then
        log_with_timestamp "Tunnel exited normally"
        break
    else
        log_with_timestamp "Tunnel crashed (exit code: $exit_code), restarting in 10 seconds..."
        sleep 10
    fi
done
EOF

chmod +x start_tunnel.sh

# Create systemd service (Linux)
if command -v systemctl &> /dev/null; then
    log_info "Creating systemd service..."

    cat > vscode-tunnel.service << EOF
[Unit]
Description=VS Code Remote Tunnel
After=network.target

[Service]
Type=simple
User=$USER
WorkingDirectory=$PWD
ExecStart=$PWD/start_tunnel.sh $TUNNEL_NAME
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
EOF

    log_info "To install as system service:"
    echo "  sudo cp vscode-tunnel.service /etc/systemd/system/"
    echo "  sudo systemctl enable vscode-tunnel"
    echo "  sudo systemctl start vscode-tunnel"
fi

# Configuration summary
cat > tunnel_info.md << EOF
# VS Code Remote Tunnel Configuration

## Access Information
- **Tunnel Name**: $TUNNEL_NAME
- **Access URL**: https://vscode.dev/tunnel/$TUNNEL_NAME
- **Local Access**: http://localhost:8000

## Mobile Access
1. **Browser**: Open https://vscode.dev/tunnel/$TUNNEL_NAME
2. **GitHub Mobile**: Use Codespaces integration
3. **Direct**: Any device with internet access

## Commands
\`\`\`bash
# Start tunnel manually
./start_tunnel.sh

# Start tunnel with custom name
./start_tunnel.sh my-custom-name

# Check tunnel status
code tunnel status

# Stop tunnel
pkill -f "code tunnel"
\`\`\`

## Security
- Authentication via GitHub/Microsoft account
- Encrypted connection (TLS 1.3)
- Access control via repository permissions
- Auto-logout after inactivity

## Troubleshooting
- Check logs: \`tail -f tunnel.log\`
- Restart service: \`sudo systemctl restart vscode-tunnel\`
- Manual start: \`./start_tunnel.sh\`
EOF

log_success "🎉 VS Code Remote Tunnels configured!"
echo ""
echo "📱 Mobile Access Instructions:"
echo "1. Start tunnel: ./start_tunnel.sh"
echo "2. Follow authentication prompts"
echo "3. Access from mobile: https://vscode.dev/tunnel/$TUNNEL_NAME"
echo ""
echo "📋 Next steps:"
echo "   - Read: tunnel_info.md"
echo "   - Start: ./start_tunnel.sh"
echo "   - Test: Open tunnel URL on mobile device"
echo ""

# Offer to start tunnel now
read -p "Start tunnel now? (y/n): " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    log_info "Starting tunnel..."
    ./start_tunnel.sh "$TUNNEL_NAME"
fi
