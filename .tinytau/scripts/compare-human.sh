#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

HUMAN_REPO="$(awk -F': *' '/^human-repo:/ {print $2}' .tinytau/config.yml | sed 's/#.*//; s/[[:space:]"\r]//g')"
HUMAN_DIR="$(awk -F': *' '/^human-directory:/ {print $2}' .tinytau/config.yml | sed 's/#.*//; s/[[:space:]"\r]//g; s:^/*::; s:/*$::')"
HUMAN_SHA="$(awk -F': *' '/^human-sha:/ {print $2}' .tinytau/sync.yml | sed 's/#.*//; s/[[:space:]"\r]//g')"

echo "human-repo=${HUMAN_REPO} human-directory=/${HUMAN_DIR} human-sha=${HUMAN_SHA}"

AI_REGEX='(.*/)?[^/]*-ai(\.[^/.]*)?$'

if [ -z "${HUMAN_SHA}" ] || [ "${HUMAN_SHA}" = "null" ]; then
  if git rev-parse --verify -q HEAD:roadmap >/dev/null; then
    extra="$(git -c core.quotepath=false ls-tree -r --name-only HEAD:roadmap | grep -vE "^${AI_REGEX}" || true)"
    if [ -n "${extra}" ]; then
      echo "FAIL: human-sha is null, but human-authored files exist under roadmap/:"
      echo "${extra}"
      exit 1
    fi
  fi
  echo "PASS: human-sha is null and roadmap/ has no human-authored files."
  exit 0
fi

if ! git cat-file -e "${HUMAN_SHA}^{commit}" 2>/dev/null; then
  git fetch --depth 1 "https://github.com/${HUMAN_REPO}.git" "${HUMAN_SHA}"
fi

UPSTREAM="${HUMAN_SHA}${HUMAN_DIR:+:${HUMAN_DIR}}"
git rev-parse --verify -q "${UPSTREAM}" >/dev/null || {
  echo "FAIL: ${UPSTREAM} not found"
  exit 1
}

if ! git rev-parse --verify -q HEAD:roadmap >/dev/null; then
  echo "FAIL: roadmap/ directory does not exist in HEAD."
  git -c core.quotepath=false ls-tree -r --name-only "${UPSTREAM}"
  exit 1
fi

# Diff upstream tree vs HEAD:roadmap, ignoring AI-maintained (*-ai.*) files
diff_out="$(git -c core.quotepath=false diff --name-status --no-renames "${UPSTREAM}" HEAD:roadmap | grep -vE "^[^[:space:]]+[[:space:]]+${AI_REGEX}" || true)"
if [ -n "${diff_out}" ]; then
  echo "FAIL: roadmap/ human-authored files differ from ${UPSTREAM}:"
  echo "${diff_out}"
  exit 1
fi

count="$(git ls-tree -r --name-only "${UPSTREAM}" | wc -l | tr -d ' ')"
echo "PASS: ${count} human-authored files in roadmap/ match ${UPSTREAM} byte-for-byte."
