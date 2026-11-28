---
name: Verification and CI Check Guide
description: Defines local Lean verification standards, the GitHub Actions CI workflow, and how to check CI status and blocking failures.
---

## Local Lean Verification

Lean verification must satisfy the checks enforced by the **Build** job in [TinyTau CI](/.github/workflows/ci.yml):

1. **Warning-Free Build**: `lake build --wfail` succeeds with zero errors and zero warnings (`build-args: "--wfail"`).
2. **Standard Axioms Only**: All declarations depend only on `propext`, `Classical.choice`, and `Quot.sound` (`axiom-audit-allow: "propext,Classical.choice,Quot.sound"`). Do not leave `sorry` / `admit` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`), or custom `axiom`s; CI verifies this via `axiom-audit`.

## GitHub Actions CI

[TinyTau CI](/.github/workflows/ci.yml) is the **only blocking CI workflow** (other workflows in the repository are non-blocking and ignored by the worker). It runs on pushes to the main branch and on pull requests.

The roadmap comparison and rendering scripts require Mike Farah's `yq` v4 when run locally (preinstalled on the GitHub-hosted Ubuntu 24.04 runner; see [yq installation](https://github.com/mikefarah/yq#install)).

- **`compare-human`** compares human-authored files in `roadmap/` against the upstream tree pinned in [`.tinytau/sync.yml`](/.tinytau/sync.yml), using the ownership rules in [`schema/roadmap.md`](/.tinytau/schema/roadmap.md).
- **`Build`** runs [Local Lean Verification](#local-lean-verification) (`lean-action`). On pushes to the main branch, it also renders the roadmap with Quarto, builds API documentation with `docgen-action`, rewrites doc links, and uploads the site artifact.
- **`Pages`** deploys the site artifact to GitHub Pages.
- **`Add Tag`** tags Lean toolchain updates on pushes to existing branches alongside **`Pages`** after **`Build`** succeeds. It uses `continue-on-error: true` and is non-blocking.

## Checking CI Status

Query recent [TinyTau CI](/.github/workflows/ci.yml) runs on the current branch (`<branch>`):

```sh
gh run list --workflow ci.yml --branch <branch> --limit 10 --json databaseId,status,conclusion,createdAt,headSha,url
```

(Pass `--limit 1` when only the latest run is needed.)

- **Failing (blocking)**: The latest run has `status: completed` and a failing `conclusion` (`failure`, `timed_out`, or `startup_failure`). This blocks new work and triggers `Fix` mode.
- **Active**: Any listed run has a `status` other than `completed`. Non-fix auto-pushes wait until no runs are active.
- **Inspecting logs**: Run `gh run view <run-id> --log-failed` to diagnose a failing run.
