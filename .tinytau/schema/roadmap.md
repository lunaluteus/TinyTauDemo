---
name: Roadmap Structure
description: Defines file ownership, .qmd conventions, and metadata pairing under roadmap/.
---

## Ownership Rule

- **Human-authored files** (stem does **not** end with `-ai`): Includes `.qmd`, `.tex`, `.md`, `.bib`, `_quarto.yml`, `.tauwanted`, figures, and any other source assets. These files are **strictly read-only** for AI agents and are updated only via verbatim upstream `Sync`.
- **AI-maintained files** (stem ends with `-ai`): Every file created or edited by an AI agent under `roadmap/` must carry `-ai` before its extension (e.g., `*-ai.qmd`, `*-ai.yml`).

## Formalization Scope (`tinytau: true` and `.tauwanted`)

Whether a human `<stem>` (file path without extension) is a formalization target is determined by its merged frontmatter and `.tauwanted` rules (see [`schema/metadata.md`](/.tinytau/schema/metadata.md) for field and pattern schemas):

- **Resolution Rule**:

  - An explicit `tinytau: false` in `<stem>`'s merged frontmatter overrides `.tauwanted`.
  - Otherwise, if `tinytau: true` appears in `<stem>`'s merged frontmatter, or any non-excluded file sharing `<stem>` matches `.tauwanted`, **all** sibling files sharing `<stem>` (e.g., `.pdf`, `.tex`, `.png`, `.qmd`) are treated as formalization targets.
  - When `<stem>` is opted in, `Sync` maintains `<stem>-ai.qmd` and `<stem>-ai.yml` to coordinate formalization details—for example, storing OCR'd `::: {#id}` targets for `.pdf` or image sources.
  - Unwanted human files remain read-only reference context in `roadmap/` without `*-ai.qmd` or `*-ai.yml`.

## Conventions for `.qmd` Files

### Human-Authored `.qmd`

Minimal conventions recommended for human authors:

- Include frontmatter (`title`, `description`/`abstract`, and optional `tinytau`) per [`schema/metadata.md`](/.tinytau/schema/metadata.md) so agents can scan files progressively.
- Wrap trackable definitions, lemmas, propositions, and theorems in fenced divs with explicit IDs, e.g. `::: {#thm-main}`, `::: {#def-basic}`, `::: {#lem-aux}`, `::: {#prp-key}`.

### Human-Authored other files

No special conventions are required. For example, you may include a `.pdf` paper in `roadmap/` for reference, and the agent may OCR and parse it into a `*-ai.qmd` file. Frontmatter and formalization targets could be interpreted there.

### AI-Authored `*-ai.qmd`

- Include `title` and `description` (or `abstract`) frontmatter per [`schema/metadata.md`](/.tinytau/schema/metadata.md).
- Use fenced divs (`::: {#id}`) for any new auxiliary targets, and state which human target(s) each file or target serves.

## Metadata Pairing

Each roadmap document uses a single YAML sidecar file (`*-ai.yml`) in the same directory:

- **Human file + optional AI companion**: `roadmap/path/<stem>.<ext>` (e.g., `topic.qmd`) and `roadmap/path/<stem>-ai.qmd` share `roadmap/path/<stem>-ai.yml`.
- **Standalone AI file**: `roadmap/path/<stem>-ai.qmd` uses `roadmap/path/<stem>-ai.yml`.
