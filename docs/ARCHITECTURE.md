# Architecture

This document provides a high‑level view of the CERTEUS platform’s
architecture and links to deeper design records.

## Core Components

- Truth Engine: formal reasoning core producing proof‑carrying outputs.
- ProofGate: verification and enforcement at system boundaries.
- Ledger Service: tamper‑evident proof anchoring and audit trail.
- Boundary Service: ingress/egress controls and redaction flows.

## Intelligence Modules

- CFE: geometry‑of‑meaning reasoning on semantic manifolds.
- lexQFT: legal/regulatory argument tunneling and barrier analysis.
- QTMP: quantum‑inspired measurement of decision states.

## Client Interfaces

- Cockpit (Web), Desktop, Mobile, SDKs (Python/TS/Go).

## Infrastructure

- Kubernetes, OpenTelemetry, Prometheus/Grafana, CI gates.

## Diagrams & ADRs

- Architecture Overview ADR: [adr/000-architecture-overview.md](adr/000-architecture-overview.md)
- Redaction Flow: [diagrams/redaction_flow.md](diagrams/redaction_flow.md)
- Publish Flow: [diagrams/publish_flow.md](diagrams/publish_flow.md)

