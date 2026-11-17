#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

OUT_DIR="$REPO_ROOT/_site/roadmap"
FILTER_PATH="$REPO_ROOT/.tinytau/scripts/tinytau.lua"

WORK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/tinytau-roadmap.XXXXXX")"
trap 'rm -rf "$WORK_DIR"' EXIT

mkdir -p "$WORK_DIR/roadmap"
cp -r roadmap/. "$WORK_DIR/roadmap/"

# Ensure a root _quarto.yml exists so --output-dir is always respected by Quarto
if [ ! -f "$WORK_DIR/roadmap/_quarto.yml" ] && [ ! -f "$WORK_DIR/roadmap/_quarto.yaml" ]; then
  cat << 'EOF' > "$WORK_DIR/roadmap/_quarto.yml"
project:
  type: default

format:
  html: default
EOF
fi

cat << EOF > "$WORK_DIR/tinytau-filter.yml"
filters:
  - at: pre-ast
    path: "$FILTER_PATH"
EOF

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

quarto render "$WORK_DIR/roadmap" \
  --to html \
  --output-dir "$OUT_DIR" \
  --metadata-file "$WORK_DIR/tinytau-filter.yml"

echo "Rendered roadmap into $OUT_DIR"
