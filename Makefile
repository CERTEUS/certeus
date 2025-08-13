.PHONY: test run
test:
	uv run pytest -q || pytest -q
run:
	uv run python -m services.api_gateway.main || python -m services.api_gateway.main
