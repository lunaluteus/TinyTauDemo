---
name: TinyTau Initialization (`tinytau doctor`)
description: Run a diagnostic self-check of configuration, upstream access, and local tooling, explain each tool's role and necessity, and help initialize the project.
---

## Doctor Self-Check

First read [`README.md`](/README.md), [`.tinytau/config.yml`](/.tinytau/config.yml), [`.tinytau/sync.yml`](/.tinytau/sync.yml), and [`guide/tooling.md`](/.tinytau/guide/tooling.md), then inspect the local environment:

### Repository & Upstream Access

- **Git & Checkout** *(Required)*: Run `git --version`, `git status`, and `git remote -v` to confirm Git works and check the local working tree. If `gh.auto-push` is `true` in [`.tinytau/config.yml`](/.tinytau/config.yml), also check whether the current branch has an upstream tracking branch (`git rev-parse --abbrev-ref --symbolic-full-name @{u}`).
- **TinyTau Config** *(Required for `Sync`)*: Check whether [`.tinytau/config.yml`](/.tinytau/config.yml) still contains sample placeholders, and test upstream read access:

  ```sh
  git ls-remote https://github.com/<human-repo>.git <human-branch>
  ```

- **Upstream `TauCeti` Tags** *(Required when `bump: true`; Optional otherwise)*: If `bump` is `true` in [`.tinytau/config.yml`](/.tinytau/config.yml), check tag access:

  ```sh
  git ls-remote --tags --refs https://github.com/TauCetiProject/TauCeti.git "refs/tags/v*"
  ```

### Local Toolchain

- **Lean 4 & Lake** *(Required for `Fix`, `Bump`, `Refactor`, and `Feat`)*: Check `lean-toolchain`, `lakefile.toml` (or `lakefile.lean`), and `lake --version`. Also note if the project still uses a template library name.
- **Search (`rg` / `grep`)** *(Recommended)*: Check `rg --version` or `grep --version` for fast searching across `roadmap/`, Mathlib, and Tau Ceti sources.
- **`lean-lsp-mcp`** *(Optional)*: Check whether `lean-lsp-mcp` is available for fine-grained interactive Lean diagnostics and goal inspection.
- **GitHub CLI (`gh`)** *(Optional)*: Check `gh --version` and `gh auth status`. Inform the user that `gh` is optional and enables the `gh.*` features in [`.tinytau/config.yml`](/.tinytau/config.yml) (`gh.fix-ci`, `gh.auto-push`, and `gh.push-min-interval`).

## Report Format

Present the doctor results to the user in a concise summary table with columns:

| Item | Status | Necessity | Purpose |
| :--- | :--- | :--- | :--- |

Include a short note summarizing any placeholder configuration or missing tools, and clearly distinguish required tools from optional ones.

## Guided Setup & Environment Assistance

After reporting the doctor summary, offer to help the user with any of the following setup steps:

- **Install or Fix Missing Tools**: Give concise OS-specific setup instructions for missing required tools and any optional tools the user chooses to enable. Offer to re-run the affected check.

- **Initialize the Lean Library**: If the Lake config still uses a template library name (or the user asks to rename the Lean library), ask for their desired UpperCamelCase library name `<ProjectName>`, then:

  1. Update `name`, `defaultTargets`, and `[[lean_lib]] name` in `lakefile.toml` (or `lakefile.lean`).
  2. Rename the root `.lean` file and library directory to `<ProjectName>.lean` and `<ProjectName>/`, updating all `import` paths accordingly.
  3. **Initialize the Lean Toolchain**: `lake update` to refresh the Lean toolchain and dependencies. Then verify the renamed library per [`guide/build.md`](/.tinytau/guide/build.md).

- **Configure `.tinytau/config.yml`**: Guide the user through configuring [`.tinytau/config.yml`](/.tinytau/config.yml) and replacing its sample placeholders (and any matching placeholder headers in existing Lean files).

- **Offer to Run the First `Sync`**: If everything is settled, offer to run the first `Sync` to initialize the local `roadmap/` with the human-authored repository.

- **Configure documentation & GitHub Pages settings**: Remind the user to enable GitHub Pages in their repository settings (**Settings → Pages → Build and deployment → Source: GitHub Actions**) so [`.github/workflows/pages.yml`](/.github/workflows/pages.yml) can build and deploy the site on `push` to the main branch. Ask whether they want to adjust `gh.fix-ci`, `gh.auto-push`, or `gh.push-min-interval` (to check CI before work and throttle how often worker commits trigger Pages builds), or set `quarto-profile` (`--profile`) in [`.tinytau/config.yml`](/.tinytau/config.yml).