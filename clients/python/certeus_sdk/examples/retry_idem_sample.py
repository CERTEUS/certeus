#!/usr/bin/env python3
from __future__ import annotations

import uuid

from certeus_sdk.client import CerteusClient


def main() -> int:
    def idem() -> str:
        return f"cli-{uuid.uuid4()}"

    cli = CerteusClient(
        tenant_id="sdk-demo",
        retries=2,
        backoff_sec=0.1,
        idem_key_factory=idem,
    )
    print(cli.health())
    # Idempotent allocate + publish alias
    print(cli.set_quota("sdk-demo", 5))
    print(cli.allocate(2))
    # publish alias (no strict proof-only expected in dev)
    print(
        cli._post(
            "/v1/proofgate/publish",
            json_body={"pco": {"hello": True}, "budget_tokens": 2},
        ).json()
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
