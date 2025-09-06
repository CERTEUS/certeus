#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "$0")/.." && pwd)
OUT_DIR="$ROOT_DIR/out/proof_artifacts"

echo "[i] Przygotowuję katalog wyjściowy: $OUT_DIR"
rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

echo "[i] Generuję artefakty dowodowe (simulate: drat, lfsc, inputs, receipt)"
python "$ROOT_DIR/scripts/generate_proofs.py" \
  --out "$OUT_DIR" \
  --mode simulate \
  --formats drat lfsc \
  --with-inputs \
  --receipt

echo "[i] Zapisuję sumy SHA256 do plików *.sha256"
(
  cd "$OUT_DIR"
  sha256sum z3.drat > z3.drat.sha256
  sha256sum cvc5.lfsc > cvc5.lfsc.sha256
)

echo "[i] Weryfikuję pliki dowodów przeciwko *.sha256"
python "$ROOT_DIR/scripts/check_proofs.py" --dir "$OUT_DIR"

echo "[i] Uruchamiam wybrane testy pytest dla proofs"
pytest -q "$ROOT_DIR/tests/truth/test_solvers.py::test_generate_proofs_function_creates_expected_artifacts" \
          "$ROOT_DIR/tests/truth/test_solvers.py::test_generate_proofs_cli_smoke_test"

echo "[✓] Proofs suite ukończona"

