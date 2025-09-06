# ============================================================================
# CERTEUS - Remote Development Setup Guide
# ============================================================================
# PL: Przewodnik konfiguracji zdalnego programowania
# EN: Remote development configuration guide
# ============================================================================

## 🌍 **VS Code Remote Development Options**

### **Option 1: GitHub Codespaces (OBECNIE AKTYWNE ✅)**
```bash
# Already running in Codespaces!
# Access via: https://github.com/codespaces

# Mobile access:
# - iOS: GitHub Mobile app → Codespaces
# - Android: GitHub Mobile app → Codespaces
# - Any browser: github.com/codespaces
```

### **Option 2: VS Code Remote Tunnels (RECOMMENDED 🚀)**
```bash
# Install VS Code CLI with tunnel support
curl -Lk 'https://code.visualstudio.com/sha/download?build=stable&os=cli-alpine-x64' --output vscode_cli.tar.gz
tar -xzf vscode_cli.tar.gz
./code tunnel --accept-server-license-terms

# Access from anywhere:
# URL: https://vscode.dev/tunnel/<machine-name>
# Mobile: Works perfectly on phones/tablets
```

### **Option 3: GitHub CLI + Codespaces**
```bash
# Current setup - already available!
gh codespace list                    # List your codespaces
gh codespace code                    # Open in VS Code desktop
gh codespace ssh                     # SSH access
gh codespace ports                   # Check forwarded ports

# Mobile access via GitHub app
```

### **Option 4: SSH + Port Forwarding**
```bash
# Setup SSH tunnel for any server
ssh -L 8080:localhost:8000 user@server
# Then access via: http://localhost:8080

# VS Code Remote SSH extension
code --install-extension ms-vscode-remote.remote-ssh
```

## 📱 **Mobile Development Experience**

### **Best Options for Mobile:**

#### **🥇 1. GitHub Codespaces (Mobile App)**
- ✅ Native mobile interface
- ✅ Touch-optimized editor
- ✅ Voice input support
- ✅ Offline sync capabilities
- ✅ No setup required

#### **🥈 2. VS Code Remote Tunnels (vscode.dev)**
- ✅ Full VS Code in browser
- ✅ All extensions work
- ✅ Real-time collaboration
- ✅ Persistent sessions
- ✅ Works on any device

#### **🥉 3. Web-based IDEs**
- ✅ GitHub.dev (github.com → press '.')
- ✅ GitPod (gitpod.io)
- ✅ Replit (replit.com)
- ✅ CodeSandbox (codesandbox.io)

## 🚀 **Setup Instructions**

### **A. Enable VS Code Remote Tunnels**
```bash
# 1. Download VS Code CLI (if not available)
wget https://update.code.visualstudio.com/latest/cli-linux-x64/stable -O vscode-cli.tar.gz
tar -xzf vscode-cli.tar.gz

# 2. Start tunnel service
./code tunnel --name "certeus-dev" --accept-server-license-terms

# 3. Follow authentication prompts
# 4. Access via: https://vscode.dev/tunnel/certeus-dev
```

### **B. Optimize GitHub Codespaces**
```bash
# Current Codespace optimization already applied:
# - Performance settings ✅
# - Mobile-friendly UI ✅
# - Essential extensions ✅
# - Auto-save enabled ✅

# Access URLs:
# Desktop: https://github.com/codespaces
# Mobile: GitHub app → Codespaces tab
```

### **C. Setup Local Tunnel Server**
```bash
# Install code-server (alternative to VS Code tunnels)
curl -fsSL https://code-server.dev/install.sh | sh

# Start server
code-server --bind-addr 0.0.0.0:8080 --auth password

# Access via: http://your-server:8080
# Mobile-optimized interface
```

## 📊 **Comparison: Remote Development Options**

| Option | Mobile Experience | Setup Difficulty | Performance | Cost |
|--------|------------------|------------------|-------------|------|
| **GitHub Codespaces** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | $$ |
| **VS Code Tunnels** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Free |
| **code-server** | ⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ | Free |
| **SSH Remote** | ⭐⭐ | ⭐ | ⭐⭐⭐ | Free |
| **GitPod** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | $ |

## 🎯 **Recommended Setup for Mobile Coding**

### **Primary: GitHub Codespaces (Current)**
```json
{
  "status": "✅ Already active",
  "mobile_app": "GitHub Mobile → Codespaces",
  "web_access": "github.com/codespaces",
  "performance": "Optimized for mobile",
  "sync": "Automatic across devices"
}
```

### **Backup: VS Code Remote Tunnels**
```bash
# Setup on your home/work computer:
code tunnel --name "certeus-home"

# Access from mobile:
# https://vscode.dev/tunnel/certeus-home
# Full desktop VS Code experience on phone!
```

### **Emergency: GitHub.dev**
```bash
# Quick edits from any device:
# 1. Go to github.com/CERTEUS/certeus
# 2. Press '.' key
# 3. Instant VS Code in browser
# 4. Make changes, commit directly
```

## 🛡️ **Security & Best Practices**

### **Secure Remote Access:**
```json
{
  "authentication": "GitHub SSO",
  "encryption": "TLS 1.3",
  "access_control": "Repository permissions",
  "session_timeout": "Auto-logout after inactivity",
  "audit_logging": "All actions tracked"
}
```

### **Persistent GitHub Push (Everywhere)**
- Preferred: set a Codespaces User Secret once (applies to all new Codespaces)
  - Go to: https://github.com/settings/codespaces/secrets
  - Add secret name: `ADMIN_TOKEN` (or `GITHUB_PUSH_TOKEN`), value: fine‑grained PAT with repo `contents:write`
  - Our devcontainer auto-picks it up via `scripts/setup_github_auth.sh`
- Alternative: keep a local file (ignored by git):
  - `.devkeys/github_user.txt` → your GitHub login (e.g., `Certeus`)
  - `.devkeys/admin_token.txt` → PAT (scope: repo)
  - Then run: `bash scripts/setup_github_auth.sh`
- Fallback: `gh auth login` + `gh auth token` is detected automatically


### **Mobile Security:**
```json
{
  "screen_lock": "Enable device lock",
  "app_lock": "Enable GitHub app lock",
  "auto_logout": "15 minutes inactivity",
  "secure_storage": "Encrypted local cache",
  "network": "Use VPN on public WiFi"
}
```

## 📱 **Mobile Coding Tips**

### **Touch Interface Optimization:**
```json
{
  "font_size": "16px minimum",
  "touch_targets": "44px minimum",
  "gestures": "Swipe, pinch, tap",
  "keyboard": "External bluetooth recommended",
  "voice_input": "Available in Codespaces"
}
```

### **Productivity on Mobile:**
```json
{
  "shortcuts": "Learn key gestures",
  "templates": "Code snippets for common tasks",
  "voice_commits": "Voice-to-text for commit messages",
  "collaboration": "Real-time pair programming",
  "review": "Mobile-optimized PR reviews"
}
```

## 🎯 **Quick Start Guide**

### **For Immediate Mobile Coding:**
1. **Open GitHub Mobile app**
2. **Navigate to Codespaces**
3. **Select this repository**
4. **Start coding instantly! 🚀**

### **For Home/Work Computer Tunnels:**
1. **Install VS Code on your computer**
2. **Run: `code tunnel --name my-dev-machine`**
3. **Access from mobile: `vscode.dev/tunnel/my-dev-machine`**
4. **Code from anywhere! 🌍**

## 🏆 **Summary**

**You have access to BEST-IN-CLASS remote development:**

- ✅ **GitHub Codespaces** - Already active, mobile-optimized
- ✅ **VS Code Tunnels** - Can be setup for home access
- ✅ **GitHub.dev** - Instant browser-based editing
- ✅ **Mobile apps** - Native GitHub mobile experience
- ✅ **Cross-device sync** - Seamless experience everywhere

**Professional mobile development experience! 📱💻**
