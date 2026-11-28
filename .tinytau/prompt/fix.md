---
name: Worker Mode `Fix`
description: Diagnose and resolve the latest failed CI run on the current branch before taking on any other mode.
---

## Procedure

1. **Inspect Failed Run**: Using the failing run detected during mode selection in [`worker.md`](./worker.md), inspect its failure logs per [`guide/check.md`](/.tinytau/guide/check.md#checking-ci-status).

2. **Diagnose & Fix Root Cause**:

   - **`compare-human` job failure**: Restore any accidentally modified human-authored file under `roadmap/` to match `human-repo` at the recorded `human-sha`. Leave `.tinytau/sync.yml` untouched in a fix.
   - **`Build` job — Lean verification failure** (`lean-action`): Fix compilation errors, warnings, or non-standard axioms.
   - **`Build` job — documentation/site failure** (Quarto rendering, `docgen-action`, link rewriting, or Pages artifact upload) or **`Pages` job failure**: Identify the root cause.

     - If it is a network issue, ignore it and continue to the next actionable worker mode. The next submission can retry the CI run.

     - If it is a configuration issue (e.g. `lakefile.toml`, `.tinytau/config.yml`), report it to the human, then ignore it and continue to the next actionable worker mode. Configuration files should never be touched without human intervention.

     - Otherwise, it should be a fixable issue in the Lean codebase. Fix the issue and go to the next step.

3. **Self-Check & Commit**: Review the fix against the failing check's requirements and [`guide/rubrics.md`](/.tinytau/guide/rubrics.md). Commit per [`worker.md`](./worker.md#committing-work). After pushing, continue to the next actionable task while CI runs. Check the workflow result during mode selection in a later round.
