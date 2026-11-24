---
name: Worker Mode `Fix`
description: Diagnose and resolve the latest failed CI workflow run on the current branch before taking on any other mode.
---

## Procedure

1. **Inspect Failed Runs**: Using the failing workflow run(s) detected during mode selection in [`worker.md`](./worker.md) (or via `gh run list --branch <branch> --limit 20 --json databaseId,workflowName,status,conclusion,createdAt,url`), inspect the failure logs:

   ```sh
   gh run view <run-id> --log-failed
   ```

2. **Diagnose & Fix Root Cause**:

   - **`Lean Action` failure**: Fix compilation errors, warnings, or non-standard axioms per [`guide/build.md`](/.tinytau/guide/build.md).
   - **`Compare Human Roadmap` failure**: Restore any accidentally modified human-authored file to match `human-repo` at the recorded `human-sha`. Leave `.tinytau/sync.yml` untouched in a fix.
   - **`Pages` failure**: Use the failed step and [`guide/tooling.md`](/.tinytau/guide/tooling.md) to identify and fix the roadmap, API documentation, or deployment error.
   - **Other workflow failure**: They are harmless; do not attempt to fix them.

3. **Self-Check & Commit**: Review the fix against the failing check's requirements and [`guide/rubrics.md`](/.tinytau/guide/rubrics.md). Commit per [`worker.md`](./worker.md#committing-work). After pushing, continue to the next actionable task while CI runs. Check the workflow result during mode selection in a later round.
