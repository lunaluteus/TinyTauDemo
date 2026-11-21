---
name: TinyTau Worker Agent Guidelines
description: Determine the highest-priority actionable worker mode, execute it, self-check against rubrics, commit directly, and push if configured.
---

## Determining Worker Mode (Priority Order)

Human instructions take precedence over this default priority order: if the user assigns a specific mode or target, follow their instruction and treat this selection process as reference only. Otherwise, evaluate the modes below in order and pick the **first** one whose conditions hold:

### [Sync](./sync.md)

Read `human-repo`, `human-branch`, `human-directory`, and `sync-min-interval` from [`.tinytau/config.yml`](/.tinytau/config.yml), and `human-sha` (`<human-sha>`) from [`.tinytau/sync.yml`](/.tinytau/sync.yml). Fetch the latest commit on `human-branch`:

```sh
git fetch https://github.com/<human-repo>.git <human-branch>
git rev-parse FETCH_HEAD
git show -s --format=%ct FETCH_HEAD
```

Let `<latest-sha>` and `<latest-timestamp>` be the returned SHA and committer timestamp. Both conditions below must hold to trigger `Sync`:

- **Upstream Commit Time Gap**: If `human-sha` is `null`, skip the time-gap check for the first Sync; otherwise fetch `<human-sha>` if needed (`git fetch https://github.com/<human-repo>.git <human-sha>`), read its committer timestamp (`git show -s --format=%ct <human-sha>`), and require `(<latest-timestamp> - <human-timestamp>) / 3600 >= sync-min-interval`.
- **Human-Authored Files Changed**: If `roadmap` exists in `HEAD` (`git ls-tree --name-only HEAD roadmap`), diff `HEAD:roadmap` against `human-directory` at `<latest-sha>` (stripping leading/trailing slashes, e.g., `git diff --name-status HEAD:roadmap <latest-sha>:` for `/` or `... <latest-sha>:notes` for `/notes`); otherwise treat all files in `human-directory` at `<latest-sha>` as additions (`git ls-tree -r --name-only <latest-sha>:` for `/`). Ignore `*-ai.*` files in the diff. If no human-authored files (per [`schema/roadmap.md`](/.tinytau/schema/roadmap.md)) changed, skip `Sync`.

### [Bump](./bump.md)

Read `bump` from [`.tinytau/config.yml`](/.tinytau/config.yml). If `bump` is `false`, skip `Bump`. Otherwise:

- Read the currently pinned `TauCeti` revision from `lakefile.toml` (or `lakefile.lean`) and the current `lean-toolchain`.
- Query upstream `TauCeti` tags:

  ```sh
  git ls-remote --tags --refs https://github.com/TauCetiProject/TauCeti.git "refs/tags/v*"
  ```

- Keep only stable Lean release tags matching `v<major>.<minor>.<patch>` (exclude `-rc*` and any non-release suffixes). Let `<latest-upstream-tag>` be the highest `(major, minor, patch)` tag. Trigger `Bump` only if `<latest-upstream-tag>` is strictly newer than the currently pinned `TauCeti` release version.

### [Refactor](./refactor.md)

Pick one `ok: refactor` target in `*-ai.yml` or one cohesive cleanup (duplicate, unused, obsolete, slow, or under-generalized Lean code—especially declarations now in Mathlib or Tau Ceti; doc–code drift; or follow-ups noted in `*-ai.qmd`, Sync commits, or Bump commits).

### [Feat](./feat.md)

Navigate `roadmap/` per [`guide/roadmap.md`](/.tinytau/guide/roadmap.md). From `roadmap/` frontmatter and `*-ai.yml`, pick an `ok: false` (or untracked) target, preferring ready targets whose `depends` in `*-ai.yml` are all `ok: true`.

If none of these apply, run `python3 .tinytau/scripts/push.py` once to retry any deferred pushes, then report that no actionable task is available and whether commits are still pending.

## Committing Work

For each task in `Sync`, `Bump`, `Refactor`, or `Feat`:

1. **Self-Check**: Verify your changes against [`guide/rubrics.md`](/.tinytau/guide/rubrics.md).
2. **Stage & Commit**: Commit one coherent task at a time using Conventional Commits (`<type>(<optional scope>): <description>`) in the imperative present tense, starting with a lowercase letter and with no trailing period:

   - `feat(area/topic#thm-main): formalize main theorem`
   - `refactor(area/topic): deduplicate helper lemmas`
   - `sync: align AI roadmap with upstream <short-human-sha>`
   - `bump: update TauCeti to <latest-upstream-tag>`

   Include a concise commit body summarizing the purpose, design choices, and modified declarations or targets.
3. **Push (If Configured)**: Run `python3 .tinytau/scripts/push.py`. It reads `auto-push` and `push-min-interval` from [`.tinytau/config.yml`](/.tinytau/config.yml). If the interval has not elapsed, continue the work and leave the commit for a later push. If the script reports a Git error, report it without guessing a different destination or force-pushing.
