"""
Automatyczna aktualizacja docstringów modułów (PL/EN) w plikach Python,
zastępująca placeholder z apply_headers bardziej precyzyjnym opisem
na podstawie ścieżki pliku.

EN: Automatically refine PL/EN module docstrings in Python files by
replacing the generic placeholder with a path-aware description.
"""

from __future__ import annotations

import ast
from pathlib import Path

ROOTS = [
    "core",
    "services",
    "plugins",
    "kernel",
    "clients",
    "scripts",
]

PLACEHOLDER_TOKENS = (
    "CERTEUS module - please complete",
    "Moduł CERTEUS - uzupełnij",
    "Modu42 CERTEUS - uzupe",  # tolerant for CP-1250 rendering
)


def _contains_placeholder(doc: str | None) -> bool:
    if not doc:
        return False
    low = doc.lower()
    # Tolerant detection irrespective of broken diacritics/hyphens
    if ("please complete" in low) or ("certeus module" in low):
        return True
    if "modu" in low and "uzupe" in low:
        return True
    return any(tok.lower() in low for tok in PLACEHOLDER_TOKENS)


def describe(rel: str) -> tuple[str, str]:
    r = rel.replace("\\", "/")
    parts = r.split("/")

    # Exact-path special cases
    if r == "services/api_gateway/main.py":
        return (
            "Aplikacja FastAPI: montuje routery, health, CORS/OTel.",
            "FastAPI application: mounts routers, health, CORS/OTel.",
        )
    if r == "core/pco/crypto.py":
        return (
            "Krypto-pomocniki: sha256 (kanoniczne), b64url, Ed25519 (podpis/weryfikacja).",
            "Crypto helpers: canonical sha256, b64url, Ed25519 sign/verify.",
        )
    if r == "core/pco/merkle.py":
        return (
            "Merkle-DAG: konstrukcja i weryfikacja (root/leaf/ścieżki dowodu).",
            "Merkle DAG: build and verify (root/leaf/proof paths).",
        )
    if r == "core/pco/public_payload.py":
        return (
            "Public payload PCO: ekstrakcja i walidacja (bez PII).",
            "PCO public payload: extraction and validation (no PII).",
        )
    if r == "core/api.py":
        return (
            "API rdzenia CERTEUS: interfejsy wysokiego poziomu.",
            "CERTEUS core API: high-level interfaces.",
        )
    if r == "core/plugin_loader.py":
        return (
            "Ładowanie wtyczek (Domain Packs) i rejestracja zdolności.",
            "Plugin loader (Domain Packs) and capability registry.",
        )

    # Routers (FastAPI)
    if "services/api_gateway/routers/" in r and r.endswith(".py"):
        name = Path(r).stem.replace("_", " ")
        mapping = {
            "export": ("eksport artefaktów i raportów", "artifact/report export"),
            "ledger": ("publiczny ledger i dowody", "public ledger and proofs"),
            "mismatch": ("zgłoszenia rozbieżności", "mismatch tickets"),
            "pco_bundle": ("pakiety PCO", "PCO bundles"),
            "pco_public": ("publiczne PCO i JWKS", "public PCO and JWKS"),
            "preview": ("podgląd artefaktów", "artifact preview"),
            "system": ("diagnostyka/system info", "diagnostics/system info"),
            "verify": ("weryfikacja dowodów", "proof verification"),
            "well_known_jwks": ("/.well-known/jwks.json", "JWKS endpoint"),
            "chatops": ("interfejs ChatOps", "ChatOps interface"),
            "devices": ("urządzenia HDE/Q-Oracle/Entangle/Chronosync", "HDE/Q-Oracle/Entangle/Chronosync devices"),
            "dr": ("Disaster Recovery: replay/revoke", "DR: replay/revoke"),
            "ethics": ("Equity Meter / HHE", "Equity Meter / HHE"),
            "fin": ("FINENITH (quantum alpha)", "FINENITH (quantum alpha)"),
            "lexqft": ("lexqft / geometria sensu", "lexqft / geometry of meaning"),
            "mailops": ("MailOps ingest/headers", "MailOps ingest/headers"),
            "metrics": ("metryki Prometheus", "Prometheus metrics"),
            "packs": ("Domain Packs / capabilities", "Domain Packs / capabilities"),
            "upn": ("rejestr UPN", "UPN registry"),
        }
        key = Path(r).stem
        pl_en = mapping.get(key, (f"obszar '{name}'", f"'{name}' domain"))
        return (
            f"Router FastAPI dla obszaru {pl_en[0]}.",
            f"FastAPI router for {pl_en[1]}.",
        )

    # Services submodules
    if "services/ingest_service/" in r:
        stem = Path(r).stem
        desc = {
            "models": ("modele danych ingestu", "ingest data models"),
            "factlog_mapper": ("mapowanie faktów/źródeł", "fact/source mapping"),
            "ocr_pipeline": ("pipeline OCR (stub)", "OCR pipeline (stub)"),
            "contracts": ("kontrakty adapterów", "adapter contracts"),
            "local_impl": ("lokalny adapter ingestu", "local ingest adapter"),
            "ocr_injector": ("wstrzykiwanie OCR (stub)", "OCR injection (stub)"),
            "registry": ("rejestr adapterów", "adapters registry"),
        }.get(stem, ("moduł serwisu ingest", "ingest service module"))
        return (
            f"Ingest Service: {desc[0]}.",
            f"Ingest Service: {desc[1]}.",
        )

    if "services/ledger_service/" in r:
        stem = Path(r).stem
        desc = {
            "ledger": ("operacje ledger (zapis/weryfikacja)", "ledger ops (record/verify)"),
            "cosmic_merkle": ("Merkle snapshoty i dowody", "Merkle snapshots and proofs"),
        }.get(stem, ("moduł serwisu ledger", "ledger service module"))
        return (f"Ledger Service: {desc[0]}.", f"Ledger Service: {desc[1]}.")

    if r.startswith("kernel/"):
        stem = Path(r).stem
        if stem in {"z3_adapter", "cvc5_adapter"}:
            return (
                "Adapter solvera SMT (dowody/konwersja).",
                "SMT solver adapter (proofs/translation).",
            )
        if stem == "smt_translator":
            return (
                "Translator SMT: walidacja/kompilacja reguł do SMT2.",
                "SMT translator: validate/compile rules to SMT2.",
            )
        return (
            "Rdzeń (Truth Engine i translatory SMT).",
            "Core (Truth Engine and SMT translators).",
        )

    if r.startswith("plugins/") and r.endswith("/src/main.py"):
        plugin = parts[1]
        return (
            f"Wejście wtyczki {plugin} (Domain Pack).",
            f"{plugin} plugin entry (Domain Pack).",
        )

    # Fallback generic
    return (
        "Moduł projektu CERTEUS (uogólniony opis).",
        "CERTEUS project module (generic description).",
    )


def replace_module_docstring(text: str, new_pl: str, new_en: str) -> str:
    """Replace the first module docstring if it matches placeholder."""
    try:
        tree = ast.parse(text)
    except Exception:
        return text
    doc = ast.get_docstring(tree)
    if not _contains_placeholder(doc):
        return text

    # Locate docstring node
    node = tree.body[0] if tree.body else None
    if (
        not isinstance(node, ast.Expr)
        or not isinstance(getattr(node, "value", None), ast.Constant)
        or not isinstance(node.value.value, str)
    ):
        return text
    start = node.lineno - 1
    end = getattr(node, "end_lineno", node.lineno) - 1
    lines = text.splitlines(keepends=True)
    new_doc = f'"""\nPL: {new_pl}\n\nEN: {new_en}\n"""\n'
    # Replace range [start:end] inclusive
    return "".join(lines[:start] + [new_doc] + lines[end + 1 :])


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    updated = 0
    for d in ROOTS:
        p = root / d
        if not p.exists():
            continue
        for f in p.rglob("*.py"):
            rel = str(f.relative_to(root)).replace("\\", "/")
            text = f.read_text(encoding="utf-8", errors="ignore")
            pl, en = describe(rel)
            new_text = replace_module_docstring(text, pl, en)
            if new_text != text:
                f.write_text(new_text, encoding="utf-8")
                updated += 1
                print(f"[DOCSTRING] {rel}")
    print(f"Done. Updated docstrings: {updated}")


if __name__ == "__main__":
    main()
