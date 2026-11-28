#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

OUT_DIR="$REPO_ROOT/_site/roadmap"
FILTER_PATH="$REPO_ROOT/.tinytau/scripts/tinytau.lua"

WORK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/tinytau-roadmap.XXXXXX")"
trap 'rm -rf "$WORK_DIR"' EXIT

mkdir -p "$WORK_DIR/roadmap"
if [[ -e roadmap || -L roadmap ]]; then
  cp -r roadmap/. "$WORK_DIR/roadmap/"
else
  human_sha="$(yq -r '.["human-sha"] // ""' .tinytau/sync.yml)"
  if [[ -n "$human_sha" && "$human_sha" != null ]]; then
    printf 'roadmap/ is missing for synced commit %s.\n' "$human_sha" >&2
    exit 1
  fi
  cat <<'EOF' > "$WORK_DIR/roadmap/index.qmd"
---
title: Roadmap
---

The roadmap will appear here after the first sync.
EOF
fi

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

QUARTO_PROFILE=""
if [ -f .tinytau/config.yml ]; then
  QUARTO_PROFILE="$(yq -r '.["quarto-profile"] // ""' .tinytau/config.yml)"
  if [[ "$QUARTO_PROFILE" == null || "$QUARTO_PROFILE" == '~' ]]; then
    QUARTO_PROFILE=""
  fi
fi

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

QUARTO_ARGS=(
  --to html
  --output-dir "$OUT_DIR"
  --metadata-file "$WORK_DIR/tinytau-filter.yml"
)
if [ -n "$QUARTO_PROFILE" ]; then
  QUARTO_ARGS+=(--profile "$QUARTO_PROFILE")
fi

quarto render "$WORK_DIR/roadmap" "${QUARTO_ARGS[@]}"

echo "Rendered roadmap into $OUT_DIR"
