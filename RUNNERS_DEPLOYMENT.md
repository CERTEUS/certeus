**Co Dostajesz (gotowe paczki)**
- `docs/codespaces-macos-runner/codespaces-macos-runner-pack.zip`: Terraform rezerwuje EC2 Mac (`mac1.metal`) + instancję, agent przez AWS SSM instaluje Homebrew, macFUSE (cask), rejestruje GitHub self‑hosted runner jako usługę (`svc.sh install && start`), z etykietami: `self-hosted, macos, macfuse`.
- `docs/codespaces-macos-runner/codespaces-agent-pack.zip` (opcjonalnie): wcześniejszy zestaw do Linux/Windows (runner, Ansible/SSH, skrypty).

Po rozpakowaniu głównego packa w repo, dostępne są:
- `scripts/aws-find-macos-ami.sh`: pomocnik do wyboru najnowszego AMI macOS.
- `scripts/agent_up.sh`: uruchamia provisioning (Terraform), pobiera token z GitHuba i bootstrappuje hosta przez SSM.
- `scripts/agent_down.sh`: sprzątanie (Terraform destroy). Uwaga na minimalne rozliczenie hosta EC2 Mac (24h).
- `infra/aws-mac-runner/*`: moduł Terraform do EC2 Mac + SSM.

**Start w Codespaces — jeden skrypt**
- Skopiuj pliki z paczki do repo (root) i otwórz je w Codespaces. W tym repo pliki są już rozmieszczone w `scripts/` i `infra/aws-mac-runner/`.
- W terminalu ustaw zmienne i wybierz AMI:
  - `export AWS_REGION=eu-central-1`
  - `export AWS_AZ=eu-central-1a`
  - `bash scripts/aws-find-macos-ami.sh | head -n 5`  # wybierz najnowsze AMI_ID
  - `export AMI_ID=ami-XXXXXXXXXXXXXXX`
  - `export GH_TOKEN=ghp_...`  # scopes: `repo`, `workflow`
  - `export GITHUB_REPOSITORY=OWNER/REPO`  # np. `CERTEUS/certeus`
- Skonfiguruj dostęp do AWS w Codespaces:
  - `aws configure sso`  (lub: `aws configure`)
- Odpal agenta:
  - `bash scripts/agent_up.sh`

Agent robi za Ciebie:
- Stawia host + instancję macOS (Terraform → EC2 Mac + dedykowany host).
- Pobiera ephemeral token runnera z GitHuba (API repo → registration‑token).
- Wysyła przez SSM zdalny bootstrap (Homebrew, macFUSE, Actions runner + usługa).
- Po kilku minutach runner będzie widoczny w GitHub → repo → Settings → Actions → Runners.

Źródła i dokumentacja: Dokumentacja AWS, support-classic.lucidlink.com, GitHub Docs.

**Sprzątanie kiedy chcesz**
- `bash scripts/agent_down.sh`
- Uwaga: host EC2 Mac ma minimalne rozliczenie 24h.

**Twarda Granica Automatyzacji (żeby było „jak jest”)**
- macFUSE to kext. Na macOS trzeba go zatwierdzić; na Apple Silicon dodatkowo wymaga Reduced Security z Recovery. Tego nie da się kliknąć zdalnie skryptem, jeśli nie masz odpowiednio skonfigurowanego MDM/DEP.
- Paczka zrobi wszystko dookoła (instalacja, runner, usługa), ale samą akceptację musisz mieć polityką MDM lub jednorazowo potwierdzić w UI.
- Wsparcie: Apple, simplemdm.com, GitHub.

**Jak Mieć Pełne Zero‑Klik**
- Intel (`mac1.metal`) + UAMDM (Jamf/Kandji) z profilem Kernel Extension Policy dla macFUSE → MDM może whitelisto­wać zespół/ID rozszerzenia i obyć się bez „Allow”.
- W paczce zostawione jest miejsce na dołożenie calli do API MDM (gdy podasz credsy).
- Na Apple Silicon i tak pozostaje wymóg „Reduced Security” z Recovery (wymóg Apple). Wsparcie Apple.

**Drobne Wskazówki do CI**
- W workflow dodaj: `runs-on: [self-hosted, macos, macfuse]`.
- Runner działa jako usługa (`svc.sh install/start/status`). Jeśli kiedyś padnie — te same komendy go wstawią i odpalą ponownie (GitHub Docs).

**Dlaczego To Jest „Codespaces‑Only”?**
- Wszystko uruchamiasz z Codespaces: Terraform → AWS, SSM do zadań na macOS, GitHub API do tokenu runnera.
- Żadnych ręcznych loginek po SSH, żadnego ręcznego kopiowania plików.
- Jedyna „ręczna” rzecz, której nie przeskoczymy, to polityki Apple dot. kextów (macFUSE) — bez MDM nie da się tego potwierdzić skryptem.

**Wymagania w Codespaces (narzędzia)**
- `aws` CLI z dostępem (SSO lub klucze), `terraform`, `jq`, `curl`. Jeśli czegoś brakuje, doinstaluj zgodnie z polityką workspacu.

**Weryfikacja Działania**
- Sprawdź runner w GitHub: repo → Settings → Actions → Runners (powinien być online z etykietami `self-hosted, macos, macfuse`).
- Podgląd logów komendy SSM: `aws ssm list-command-invocations --command-id <ID> --details --region $AWS_REGION` (ID zwraca `agent_up.sh`).
