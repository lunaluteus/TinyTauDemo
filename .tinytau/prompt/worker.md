---
name: TinyTau Worker Agent (`tinytau worker`)
description: Determine the highest-priority actionable worker mode, execute it, self-check against rubrics, commit directly, and push if configured.
---

## Determining Worker Mode (Priority Order)

Human instructions take precedence over this default priority order: if the user assigns a specific mode or target, follow their instruction and treat this selection process as reference only. Otherwise, evaluate the modes below in order and pick the **first** one whose conditions hold.

In the worker workflow, unless explicitly instructed by the user:

- Except in `Bump` mode, do not add, remove, or modify Lean/Lake dependencies or toolchain pins (`lakefile.toml`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`). Do not `lake update`.

- In `Sync` mode you can update `.tinytau/sync.yml`. Otherwise, do not change CI, prompts, or any other configuration files in `.tinytau/` and `.github/`.

### [Fix](./fix.md)

Read `gh.fix-ci` from [`.tinytau/config.yml`](/.tinytau/config.yml). If `gh.fix-ci` is `false`, or if `gh` is unavailable or unauthenticated (`gh auth status` fails), or if `HEAD` is detached, skip `Fix`. Otherwise, inspect the latest CI run on the current branch (`<branch>`) per [`guide/check.md`](/.tinytau/guide/check.md#checking-ci-status). If it is failing, trigger `Fix` first.

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

If none of these apply, check [Automatic Pushes](#automatic-pushes) to flush any unpushed local commits if a push is due, then report that no actionable task is currently available (noting whether any commits remain local).

## Committing Work

For each task in `Fix`, `Sync`, `Bump`, `Refactor`, or `Feat`:

1. **Self-Check**: Verify your changes against [`guide/rubrics.md`](/.tinytau/guide/rubrics.md).
2. **Stage & Commit**: Commit one coherent task at a time using Conventional Commits (`<type>(<optional scope>): <description>`) in the imperative present tense, starting with a lowercase letter and with no trailing period:

   - `fix(area/topic): resolve Lean build failure`
   - `feat(area/topic#thm-main): formalize main theorem`
   - `refactor(area/topic): deduplicate helper lemmas`
   - `sync: align AI roadmap with upstream <short-human-sha>`
   - `bump: update TauCeti to <latest-upstream-tag>`

   Include a concise commit body summarizing the purpose, design choices, and modified declarations or targets.
3. **Push (If Due)**: Follow [Automatic Pushes](#automatic-pushes) to push if configured and any active CI / throttle checks are satisfied.

## Automatic Pushes

Read `gh.auto-push` and `gh.push-min-interval` from [`.tinytau/config.yml`](/.tinytau/config.yml):

- If `gh.auto-push` is `false` (or unset), if there are no unpushed local commits (check e.g. `git status -sb`), if `gh` is unavailable or unauthenticated (`gh auth status` fails), or if `HEAD` is detached, leave everything local and skip pushing.
- Otherwise, query recent CI runs on the current branch (`<branch>`) per [`guide/check.md`](/.tinytau/guide/check.md#checking-ci-status):

  1. **Bypass throttle on CI failure**: If the task just committed was `Fix`, or if the latest run is failing, the `gh.push-min-interval` throttle does **not** apply—push immediately via `git push` (never force-pushing; if pushing fails or no upstream is configured, report the error instead of guessing).
  2. **Wait for active CI**: Otherwise, if any listed run is active, do **not** push yet—keep the commits local.
  3. **Check creation-time throttle**: If all listed runs are `completed` (or if no runs exist yet on `<branch>`): a push is due if no runs exist yet, `gh.push-min-interval` is `0`, or `now - latest_createdAt >= gh.push-min-interval * 60` (in seconds, using the newest run's `createdAt`). Otherwise, keep the commits local.
  4. **Push when due**: Run `git push` (never force-pushing; if pushing fails or no upstream is configured, report the error instead of guessing).
