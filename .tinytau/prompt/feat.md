---
name: Worker Mode `Feat`
description: Formalize an unclaimed roadmap/ target while keeping AI documentation, metadata, and Lean 4 code synchronized.
---

## Procedure

1. **Search Upstream First**: Search Mathlib, Tau Ceti, and the local repository for existing definitions, structures, and lemmas you can reuse.

2. **Read Context**: Read the target's `::: {#id}` block (and surrounding human prose), its `depends` in `*-ai.yml`, and the Lean modules for those dependencies.

3. **Write Docs & Lean Together**:

   - If the human text is high-level or needs intermediate theory not in Mathlib or Tau Ceti, add it to `roadmap/path/<stem>-ai.qmd` (or a standalone `*-ai.qmd` file under `roadmap/`) with `title`/`description` frontmatter, explicit `::: {#id}` targets, and a note naming the human target(s) each item serves.
   - Write complete, clean Lean 4 definitions and proofs (no `sorry` or custom `axiom`s). Whenever a Lean docstring or comment cites a `roadmap/` path or target ID, pin it to the current `HEAD` commit SHA (e.g., `/roadmap/area/topic.qmd#thm-main @ <commit-sha>`).

4. **Build**: Run `lake build` until it succeeds with zero errors.

5. **Update Metadata**: Update `*-ai.yml` per [`schema/metadata.md`](/.tinytau/schema/metadata.md) in the same commit—set `ok: true` with verified `/docs/...` paths in `docs` and a concise `comment` for completed targets, and `ok: false` with `docs: []` for any remaining stepping-stone targets (keeping `depends` up to date).

6. **Self-Check & Commit**: Review your changes against [`guide/rubrics.md`](/.tinytau/guide/rubrics.md) and commit per [`worker.md`](./worker.md#committing-work).
