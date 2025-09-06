# ============================================================================
#  CODESPACES macOS RUNNER PACK  |  ForgeHeader v1
#  PL: Zestaw do postawienia self-hosted runnera macOS z poziomu Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, rejestracja runnera przez GH API.
#  EN: End-to-end self-hosted macOS runner from Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, runner registration via GH API.
#
#  File      : scripts/agent_up.sh
#  Author    : Radosław Skarżycki (Radziu)
#  Version   : 0.2.0
#  Date (UTC): 2025-09-06T17:40:49Z
#  License   : MIT
#  Repo      : <fill-after-commit>
# ============================================================================

#!/usr/bin/env bash
set -euo pipefail

# Required env:
: "${AWS_REGION:?Set AWS_REGION}"
: "${AWS_AZ:?Set AWS_AZ}"
# AMI_ID: spróbuj wykryć automatycznie jeśli nie ustawiono
if [[ -z "${AMI_ID:-}" ]]; then
  if command -v aws >/dev/null 2>&1; then
    echo "[i] AMI_ID nie ustawione — wyszukuję najnowsze AMI..."
    AMI_ID=$(bash "$(dirname "$0")/aws-find-macos-ami.sh" | sort -r | head -n1 | awk '{print $2}')
    if [[ -z "$AMI_ID" ]]; then
      echo "[!] Nie udało się automatycznie wykryć AMI_ID. Ustaw AMI_ID i uruchom ponownie." >&2
      exit 1
    fi
    export AMI_ID
    echo "[OK] Wybrane AMI_ID: $AMI_ID"
  else
    echo "[!] Brak aws CLI, nie mogę wykryć AMI_ID. Ustaw AMI_ID i uruchom ponownie." >&2
    exit 1
  fi
fi

: "${GITHUB_REPOSITORY:?Set GITHUB_REPOSITORY (OWNER/REPO)}"

# 1) Terraform apply
pushd infra/aws-mac-runner >/dev/null
  terraform init -upgrade
  terraform apply -auto-approve -var "region=$AWS_REGION" -var "az=$AWS_AZ" -var "ami_id=$AMI_ID"
  INSTANCE_ID="$(terraform output -raw instance_id)"
popd >/dev/null

echo "[OK] macOS instance: $INSTANCE_ID"

# 2) Get GitHub runner registration token (GH_TOKEN or gh cli fallback)
if [[ -n "${GH_TOKEN:-}" ]]; then
  TOKEN_JSON="$(curl -sS -X POST -H "Authorization: Bearer $GH_TOKEN" -H "Accept: application/vnd.github+json"   "https://api.github.com/repos/$GITHUB_REPOSITORY/actions/runners/registration-token")"
  RUNNER_TOKEN="$(echo "$TOKEN_JSON" | jq -r .token)"
else
  if command -v gh >/dev/null 2>&1 && gh auth status >/dev/null 2>&1; then
    RUNNER_TOKEN="$(gh api -X POST "repos/$GITHUB_REPOSITORY/actions/runners/registration-token" -q .token)"
  else
    echo "[ERROR] Brak GH_TOKEN oraz brak zalogowanego gh cli. Ustaw GH_TOKEN lub zaloguj gh auth login." >&2
    exit 1
  fi
fi

if [[ -z "$RUNNER_TOKEN" || "$RUNNER_TOKEN" == "null" ]]; then
  echo "[ERROR] Nie udało się pobrać tokenu runnera z GitHub" >&2
  exit 1
fi

# 3) SSM bootstrap commands (brew, jq, macfuse, actions runner)
BOOTSTRAP='
set -euxo pipefail
export PATH="/usr/local/bin:/opt/homebrew/bin:$PATH"

# Install Homebrew (non-interactive)
if ! command -v brew >/dev/null 2>&1; then
  /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)" </dev/null
  if [ -x /opt/homebrew/bin/brew ]; then
    echo "eval "$(/opt/homebrew/bin/brew shellenv)"" >> /Users/ec2-user/.zprofile || true
    eval "$(/opt/homebrew/bin/brew shellenv)"
  fi
fi

brew update || true
brew install jq || true

# Install macFUSE cask (KEXT will still need approval on many setups)
brew install --cask macfuse || true

# Prepare GitHub Actions runner
RUNNER_DIR="$HOME/actions-runner"
mkdir -p "$RUNNER_DIR"
cd "$RUNNER_DIR"

VER="$(curl -s https://api.github.com/repos/actions/runner/releases/latest | jq -r ".tag_name" | sed "s/^v//")"
curl -L -o actions-runner-osx-x64.tar.gz "https://github.com/actions/runner/releases/download/v$VER/actions-runner-osx-x64-$VER.tar.gz"
tar xzf actions-runner-osx-x64.tar.gz

./config.sh --unattended --url "https://github.com/__REPO__" --token "__TOKEN__" --labels "self-hosted,macos,macfuse"
sudo ./svc.sh install
sudo ./svc.sh start
sudo ./svc.sh status || true
'

BOOTSTRAP="${BOOTSTRAP//__REPO__/$GITHUB_REPOSITORY}"
BOOTSTRAP="${BOOTSTRAP//__TOKEN__/$RUNNER_TOKEN}"

CMD_ID="$(aws ssm send-command   --document-name "AWS-RunShellScript"   --instance-ids "$INSTANCE_ID"   --parameters commands="$BOOTSTRAP"   --query "Command.CommandId" --output text --region "$AWS_REGION")"

echo "[*] SSM Command sent: $CMD_ID"
echo "[i] Check progress: aws ssm list-command-invocations --command-id $CMD_ID --details --region $AWS_REGION"
echo "[✓] Done. Runner should appear in GitHub shortly."
