#!/usr/bin/env text

GitHub Actions Runner (Linux) — Docker Compose
=============================================

This runner registers to the private core repo and executes jobs with labels: `self-hosted,linux,docker,build`.

Do NOT commit secrets. Use `.env` (local only) or pass env at runtime.

Quick start (Linux host)
------------------------
1) Prepare token (choose ONE):
   - Ephemeral (recommended):
     - `gh api -X POST repos/CERTEUS/certeus/actions/runners/registration-token -q .token`
     - Copy the value as `RUNNER_TOKEN` into `.env`
   - PAT (less preferred):
     - Create PAT with `repo` scope; set `GITHUB_ACCESS_TOKEN` in `.env`.

2) Create `.env` from template:
   - `cp .env.example .env`
   - Fill `RUNNER_TOKEN=...` (or `GITHUB_ACCESS_TOKEN=`) and optional `RUNNER_NAME`.

3) Start runner:
   - `docker compose up -d`

4) Verify in GitHub → repo → Settings → Actions → Runners (should be online).

- Docker builds: the compose mounts `/var/run/docker.sock` so release jobs can build/push images.
- Ephemeral runner (`EPHEMERAL=true`): the container exits when job finishes; restart policy brings it back.

Windows host with Docker Desktop (optional)
------------------------------------------
If the host is Windows and you want docker builds inside the runner container, mount the Windows engine pipe instead:

```
services:
  gha-runner:
    volumes:
      - //./pipe/docker_engine://./pipe/docker_engine
    environment:
      DOCKER_HOST: npipe:////./pipe/docker_engine
```

Stop / remove
-------------
- `docker compose down -v` (removes container + volume), then rotate token.

