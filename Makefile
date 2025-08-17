# +-------------------------------------------------------------+
# |                        CERTEUS Makefile                     |
# |  PL/EN logs, color output, proofs, checks, and tests        |
# +-------------------------------------------------------------+

# -------- Cross-platform shell & utils --------
ifeq ($(OS),Windows_NT)
  # Wymuś sh.exe z Git for Windows (UWAGA: bez cudzysłowów!)
  SHELL := C:/Progra~1/Git/bin/sh.exe
  # Windowsowe odpowiedniki rm/mkdir przez PowerShell
  RM_RF = powershell -NoProfile -Command "if (Test-Path '$(1)') { Remove-Item -Recurse -Force '$(1)' }"
  MKDIR_P = powershell -NoProfile -Command "New-Item -ItemType Directory -Force '$(1)' | Out-Null"
else
  SHELL := /bin/bash
  RM_RF = rm -rf $(1)
  MKDIR_P = mkdir -p $(1)
endif

.ONESHELL:
.SHELLFLAGS := -eu -o pipefail -c

.PHONY: setup run lint clean help proofs verify test test-unit test-cli

# === CONFIG / KONFIGURACJA ===
LANG ?= pl                    # en => English messages
PYTHON ?= python
UV ?= uv
SCRIPT := scripts/generate_proofs.py
OUT_DIR := proofs

# Domyślne parametry dla proofs
format ?=
mode ?=

# === Kolory ANSI / ANSI Colors ===
COLOR_BLUE  = \033[1;34m
COLOR_GREEN = \033[1;32m
COLOR_RED   = \033[1;31m
COLOR_GRAY  = \033[0;90m
COLOR_RESET = \033[0m

# === Makro wyboru języka / Language switch ===
define MSG
$(if $(filter $(LANG),pl),$(1),$(2))
endef

# === SETUP (deps + pre-commit) ===
setup:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Instalacja zależności i pre-commit...,>> Installing deps and pre-commit...)"
	@command -v $(UV) >/dev/null 2>&1 || ( printf "$(COLOR_GRAY)%s$(COLOR_RESET)\n" "$(call MSG,>>> Instaluję uv...,>>> Installing uv...)" ; pip install uv )
	$(UV) pip install -e .[dev]
	$(UV) run pre-commit install
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Setup gotowy.,✅ Setup done.)"

# === RUN (API dev server) ===
run:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Start serwera API...,>> Starting API server...)"
	$(UV) run uvicorn services.api_gateway.main:app --reload --port 8000

# === LINT (Ruff: check + format) ===
lint:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Lint + format (Ruff)...,>> Lint + format (Ruff)...)"
	$(UV) run ruff check .
	$(UV) run ruff format .
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Lint OK.,✅ Lint OK.)"

# === CLEAN (cache/temp) ===
clean:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Czyszczenie cache...,>> Cleaning cache...)"
	@$(call RM_RF,.pytest_cache)
	@$(call RM_RF,$(OUT_DIR))
	# opcjonalnie wyczyść pycache; brak błędów na Windows (przekieruj stderr)
	@find . -type f -name '*.pyc' -delete 2>/dev/null || true
	@find . -type d -name '__pycache__' -delete 2>/dev/null || true
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Czyściej się nie da.,✅ Squeaky clean.)"

# === PROOFS (generate DRAT/LFSC) ===
proofs:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Generowanie dowodów...,>> Generating proofs...)"
	@$(call RM_RF,$(OUT_DIR))
	@$(call MKDIR_P,$(OUT_DIR))
	@if [ -n "$(format)" ] && [ -n "$(mode)" ]; then \
		printf "$(COLOR_GRAY)%s$(COLOR_RESET)\n" "$(call MSG,Format:,Format:) $(format) | $(call MSG,Tryb:,Mode:) $(mode)"; \
		$(UV) run $(PYTHON) $(SCRIPT) --out $(OUT_DIR) --formats $(format) --mode $(mode); \
	elif [ -n "$(format)" ]; then \
		printf "$(COLOR_GRAY)%s$(COLOR_RESET)\n" "$(call MSG,Format:,Format:) $(format) | $(call MSG,Tryb domyślny:,Default mode:) stub"; \
		$(UV) run $(PYTHON) $(SCRIPT) --out $(OUT_DIR) --formats $(format); \
	elif [ -n "$(mode)" ]; then \
		printf "$(COLOR_GRAY)%s$(COLOR_RESET)\n" "$(call MSG,Format domyślny:,Default formats:) drat+lfsc | $(call MSG,Tryb:,Mode:) $(mode)"; \
		$(UV) run $(PYTHON) $(SCRIPT) --out $(OUT_DIR) --mode $(mode); \
	else \
		printf "$(COLOR_GRAY)%s$(COLOR_RESET)\n" "$(call MSG,Format domyślny:,Default formats:) drat+lfsc | $(call MSG,Tryb domyślny:,Default mode:) stub"; \
		$(UV) run $(PYTHON) $(SCRIPT) --out $(OUT_DIR); \
	fi
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Dowody wygenerowane.,✅ Proofs generated.)"

# === VERIFY (DRAT + LFSC checks) ===
verify:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Weryfikacja dowodów (DRAT+LFSC)...,>> Verifying proofs (DRAT+LFSC)...)"
	@bash scripts/check_drat.sh -d $(OUT_DIR)
	@bash scripts/check_lfsc.sh -d $(OUT_DIR)
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Weryfikacja zaliczona.,✅ Verification passed.)"

# === TESTS ===
test:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Uruchamianie testów (pytest) ...,>> Running tests (pytest) ...)"
	$(UV) run pytest -q
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Testy OK.,✅ Tests OK.)"

test-unit:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Testy jednostkowe...,>> Unit tests...)"
	$(UV) run pytest -q -k "not cli"
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ Unit OK.,✅ Unit OK.)"

test-cli:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> Test CLI...,>> CLI test...)"
	$(UV) run pytest -q -k "cli"
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ CLI OK.,✅ CLI OK.)"

help:
	@printf "\n"
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "CERTEUS – $(call MSG,Polecenia Makefile,Makefile Commands)"
	@printf "  $(COLOR_GREEN)make setup$(COLOR_RESET)      – $(call MSG,Instalacja zależności i pre-commit,Install deps & pre-commit)\n"
	@printf "  $(COLOR_GREEN)make run$(COLOR_RESET)        – $(call MSG,Uruchom serwer API,Run API server)\n"
	@printf "  $(COLOR_GREEN)make lint$(COLOR_RESET)       – $(call MSG,Ruff check + format,Ruff check + format)\n"
	@printf "  $(COLOR_GREEN)make clean$(COLOR_RESET)      – $(call MSG,Wyczyść cache i dowody,Clean caches & proofs)\n"
	@printf "  $(COLOR_GREEN)make proofs$(COLOR_RESET)     – $(call MSG,Wygeneruj dowody (format=..., mode=...),Generate proofs (format=..., mode=...))\n"
	@printf "  $(COLOR_GREEN)make verify$(COLOR_RESET)     – $(call MSG,Sprawdź DRAT i LFSC (skrypty),Verify DRAT & LFSC (scripts))\n"
	@printf "  $(COLOR_GREEN)make test$(COLOR_RESET)       – $(call MSG,Uruchom wszystkie testy,Run all tests)\n"
	@printf "  $(COLOR_GREEN)make test-unit$(COLOR_RESET)  – $(call MSG,Tylko testy jednostkowe,Unit tests only)\n"
	@printf "  $(COLOR_GREEN)make test-cli$(COLOR_RESET)   – $(call MSG,Tylko test CLI,CLI test only)\n"
	@printf "\n"
	@printf "$(COLOR_GRAY)%s$(COLOR_RESET)\n" "$(call MSG,Tip:,Tip:) $(call MSG,Użyj LANG=en dla angielskich logów.,Use LANG=pl for Polish logs.)"

ci:
	@printf "$(COLOR_BLUE)%s$(COLOR_RESET)\n" "$(call MSG,>> CI: clean → lint → proofs(simulate) → verify → test-unit...,>> CI: clean → lint → proofs(simulate) → verify → test-unit...)"
	@"$(MAKE)" clean
	@"$(MAKE)" lint
	@"$(MAKE)" proofs mode=simulate
	@"$(MAKE)" verify
	@"$(MAKE)" test-unit
	@printf "$(COLOR_GREEN)%s$(COLOR_RESET)\n" "$(call MSG,✅ CI preflight OK.,✅ CI preflight OK.)"
