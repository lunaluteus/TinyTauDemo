---
name: Worker Mode `Refactor`
description: Resolve an `ok: refactor` target, technical debt, or doc-code drift before taking on new `Feat` work.
---

## Procedure

1. Refactor or repair the Lean code and update all affected `*-ai.qmd` and `*-ai.yml` entries per [`schema/metadata.md`](/.tinytau/schema/metadata.md) (set `ok: true` with verified `/docs/...` paths in `docs`, update `depends` and `comment` once resolved, or remove obsolete entries if the target was deleted).
2. Update all affected callers and any stale `roadmap/` references in Lean docstrings across the repo (re-pinning references to the current `HEAD` commit SHA).
3. Run `lake build` until it succeeds with zero errors.
4. Review your changes against [`guide/rubrics.md`](/.tinytau/guide/rubrics.md) and commit per [`worker.md`](./worker.md#committing-work).
