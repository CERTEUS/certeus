Self-hosted GitHub Actions runner (Docker, ephemeral)

- Image: myoung34/github-runner:latest
- Labels: self-hosted, linux, docker, build
- Ephemeral: true (auto-unregisters after job)

Usage

1) Generate token: Repository → Settings → Actions → Runners → New runner → Repository runner → Copy token.
2) Create .env from example:

cp infra/runner/.env.example infra/runner/.env
# edit infra/runner/.env and paste GH_RUNNER_TOKEN

3) Start:

cd infra/runner
docker compose up -d

4) Verify runner is online in Settings → Actions → Runners.

5) Stop:

docker compose down

Test job: set runs-on: [self-hosted, linux, docker, build].

