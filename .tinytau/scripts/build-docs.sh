#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

if [ "${1:-}" = "--print-cache-paths" ]; then
  python3 .tinytau/scripts/parse-lake-metadata.py --print-cache-paths
  exit 0
fi

eval "$(python3 .tinytau/scripts/parse-lake-metadata.py)"

if command -v lake >/dev/null 2>&1; then
  LAKE_BIN="lake"
else
  LAKE_BIN="$HOME/.elan/bin/lake"
fi

mkdir -p docbuild

cat << EOF > docbuild/lakefile.toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "$NAME"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$(cut -f 2 -d: lean-toolchain | tr -d '\r')"
EOF

(
  cd docbuild
  MATHLIB_NO_CACHE_ON_UPDATE=1 "$LAKE_BIN" update "$NAME"
  "$LAKE_BIN" build $DOCS_FACETS
)

mkdir -p _site
rm -rf _site/docs
cp -r docbuild/.lake/build/doc _site/docs
echo "Built doc-gen4 documentation into _site/docs"
