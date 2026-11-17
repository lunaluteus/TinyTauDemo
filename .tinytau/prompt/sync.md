---
name: Sync
description: Copy the configured human directory into roadmap/ verbatim and realign AI-maintained roadmap files. Do not edit .lean files in a Sync commit.
---

## Copy Human Files Verbatim

Using `<latest-sha>` and `human-directory` already fetched during mode selection in [`worker.md`](./worker.md):

1. Remove any human-authored files under `roadmap/` that were deleted upstream (keep all `*-ai.*` files untouched), then extract the exact upstream bytes via `git archive` (use `<latest-sha>` for `human-directory: /`, or `<latest-sha>:notes` for `/notes`):

   ```sh
   mkdir -p roadmap
   git archive <latest-sha>:<human-dir> | tar -x -C roadmap
   ```

2. Update `human-sha` in [`.tinytau/sync.yml`](/.tinytau/sync.yml) to `<latest-sha>` in the same commit.

## Realign AI-Maintained Files

Update only AI-maintained files under `roadmap/` (`*-ai.qmd` per [`schema/roadmap.md`](/.tinytau/schema/roadmap.md), and `*-ai.yml` per [`schema/metadata.md`](/.tinytau/schema/metadata.md)):

- **New wanted human file or target** (`tinytau: true` or `.tauwanted` per [`schema/roadmap.md`](/.tinytau/schema/roadmap.md)):

  - Ensure `<stem>-ai.qmd` exists to coordinate formalization details (for `.pdf`, images, or unannotated sources, OCR/extract trackable `::: {#id}` targets into `<stem>-ai.qmd` and reference the source file).
  - Initialize or update `<stem>-ai.yml` (`ok: false`, `docs: []`, and `depends` for each new `::: {#id}` target).

- **New unwanted human file**: Leave as read-only reference; do not create `*-ai.qmd` or `*-ai.yml`.

- **Unchanged target ID & meaning**: Leave existing AI files as they are.

- **Modified statement or hypothesis**: Re-check any `ok: true` formalization against the updated math. If it no longer matches, set `ok: refactor` in `*-ai.yml` (keep existing `docs` paths), describe the discrepancy in `comment`, and update `*-ai.qmd` / `depends` as needed.

- **Renamed or moved target/file**: Update `id`, `depends`, and `/roadmap/...` paths across all `*-ai.yml` and `*-ai.qmd` files, and rename paired AI files to match moved human files. If any `.lean` docstring has a commit-pinned reference to the old path/ID, set `ok: refactor` in `*-ai.yml` and note the outdated reference in `comment` (do not edit `.lean` files).

- **Deleted target or file**: Remove obsolete `depends` links. Do **not** delete verified Lean code during Sync; mark affected `*-ai.yml` entries `ok: refactor` and note the orphaned Lean code or stale `roadmap/` references in `comment` for a later `Refactor` commit.

- **Ambiguous mapping**: If a human rewrite makes correspondence unclear, **do not guess**—mark affected existing entries `ok: refactor` (or new/unlinked entries `ok: false`) and flag the ambiguity in `comment`.

## Commit the Sync

Self-check roadmap consistency against [`guide/rubrics.md`](/.tinytau/guide/rubrics.md) and commit per [`worker.md`](./worker.md#committing-work).
