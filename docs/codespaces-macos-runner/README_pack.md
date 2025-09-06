# ============================================================================
#  CODESPACES macOS RUNNER PACK  |  ForgeHeader v1
#  PL: Zestaw do postawienia self-hosted runnera macOS z poziomu Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, rejestracja runnera przez GH API.
#  EN: End-to-end self-hosted macOS runner from Codespaces.
#      Terraform (EC2 Mac), SSM bootstrap, runner registration via GH API.
#
#  File      : README.md
#  Author    : Radosław Skarżycki (Radziu)
#  Version   : 0.2.0
#  Date (UTC): 2025-09-06T17:40:49Z
#  License   : MIT
#  Repo      : <fill-after-commit>
# ============================================================================

# 🚀 Codespaces → macOS Runner (AWS) — One Command

**Cel:** z Codespaces stawiasz *prawdziwy* runner **macOS** (EC2 Mac), agent sam:
- rezerwuje Dedicated Host (mac1.metal),
- tworzy instancję macOS,
- bootstrappuje przez **AWS SSM** (brew, jq, macFUSE cask, runner),
- rejestruje runnera w repo (etykiety: `self-hosted, macos, macfuse`),
- uruchamia usługę (`svc.sh install && start`).

> **Uwaga – polityka Apple:** Załadowanie kext **macFUSE** wymaga *akceptacji/obniżenia poziomu zabezpieczeń* (zwłaszcza na Apple Silicon). Tego **nie da się** w pełni zautomatyzować bez odpowiedniego MDM/DEP. Runner i tak będzie online – testy montowania ruszą po akceptacji. (Źródła: Apple Deployment „System & Kernel Extensions” i AWS/SSM docs.)

## 0) Wymagane zmienne
W Codespaces ustaw (np. w terminalu bash):
```bash
export AWS_REGION=eu-central-1        # region z EC2 Mac
export AWS_AZ=eu-central-1a           # AZ z dostępnym mac1.metal
export AMI_ID=ami-xxxxxxxxxxxxxxxxx   # macOS AMI (patrz: scripts/aws-find-macos-ami.sh)
export GH_TOKEN=ghp_xxx               # GitHub token (scopes: repo, workflow)
export GITHUB_REPOSITORY=OWNER/REPO   # np. CERTEUS/certeus
```
Skonfiguruj AWS połączenie (SSO/keys), np.:
```bash
aws configure sso   # lub: aws configure
```

## 1) Start — jeden skrypt
```bash
bash scripts/agent_up.sh
```
Co zrobi:
1. `terraform apply` w `infra/aws-mac-runner/` (host + instancja macOS),
2. odczyta `instance_id` z `terraform output`,
3. pobierze ephemeral **runner token** z GitHub API,
4. wyśle przez **AWS SSM** komendy bootstrap na macOS (brew, macfuse cask, runner svc).

Po ~5–10 min runner pojawi się w **Settings → Actions → Runners**.

## 2) Przyjęcie macFUSE (jeśli wymagane)
- **mac1.metal (Intel):** profil MDM może auto‑zatwierdzić KEXT (UAMDM). Bez MDM zwykle wymagane jest *„Allow”* w Privacy & Security.
- **mac2.metal (Apple Silicon):** dodatkowo konieczne *Reduced Security* w trybie Recovery (ręcznie).

## 3) Sprzątanie
```bash
bash scripts/agent_down.sh
```
> **WAŻNE:** Dedicated Host dla EC2 Mac ma minimalny okres rozliczeniowy (24h).

## 4) Diagnoza
- Logi SSM Run Command → `aws ssm list-command-invocations --details ...`
- Status runnera → `~/actions-runner/svc.sh status` (na macOS)
