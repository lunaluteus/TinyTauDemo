---
name: TinyTau Initialization (`tinytau doctor`)
description: Run a diagnostic self-check of configuration, upstream access, and local tooling, explain each tool's role and necessity, and help initialize the project (including renaming ExampleLibrary and configuring Quarto/Lean environments).
---

## Doctor Self-Check

First read [`README.md`](/README.md), [`.tinytau/config.yml`](/.tinytau/config.yml), [`.tinytau/sync.yml`](/.tinytau/sync.yml), and [`guide/tooling.md`](/.tinytau/guide/tooling.md), then inspect the local environment:

### Repository & Upstream Access

- **Git & Checkout** *(Required)*: Run `git --version`, `git status`, and `git remote -v` to confirm Git works and check the local working tree.
- **TinyTau Config & `human-repo`** *(Required for `Sync`)*: Check whether [`.tinytau/config.yml`](/.tinytau/config.yml) still contains sample placeholders (`example-org/research-roadmap`), and test upstream read access:

  ```sh
  git ls-remote https://github.com/<human-repo>.git <human-branch>
  ```

- **Upstream `TauCeti` Tags** *(Required when `bump: true`; Optional otherwise)*: If `bump` is `true` in [`.tinytau/config.yml`](/.tinytau/config.yml), check tag access:

  ```sh
  git ls-remote --tags --refs https://github.com/TauCetiProject/TauCeti.git "refs/tags/v*"
  ```

### Local Toolchain

- **Lean 4 & Lake** *(Required for `Bump`, `Refactor`, and `Feat`)*: Check `lean-toolchain`, `lakefile.toml` (or `lakefile.lean`), and `lake --version`. Also note if the project still uses the template library name `ExampleLibrary`.
- **Search (`rg` / `grep`)** *(Recommended)*: Check `rg --version` or `grep --version` for fast searching across `roadmap/`, Mathlib, and Tau Ceti sources.
- **`lean-lsp-mcp`** *(Optional)*: Check whether `lean-lsp-mcp` is available for fine-grained interactive Lean diagnostics and goal inspection (not required if relying solely on `lake build`).
- **Quarto & Local Doc/CI Scripts** *(Optional)*: Check `quarto --version`, `bash --version`, and `python3 --version` (3.11+ for `parse-lake-metadata.py`). Explicitly inform the user that **Quarto (and `python3`/`build-docs.sh`) is only needed if they want to render `roadmap/` or `doc-gen4` docs locally**—if they rely on GitHub Actions (`.github/workflows/pages.yml` and `compare-human.yml`), local Quarto is unnecessary.

## Report Format

Present the doctor results to the user in a concise summary table with columns:

| Item | Status | Necessity | Purpose |
| :--- | :--- | :--- | :--- |

Include a short note summarizing any placeholder configuration (`example-org/...`, `ExampleLibrary`) or missing tools, and clearly distinguish required tools from optional ones.

## Guided Setup & Environment Assistance

After reporting the doctor summary, offer to help the user with any of the following setup steps:

- **Rename the Template Library (`ExampleLibrary`)**: If `lakefile.toml` still uses `ExampleLibrary` (or the user asks to rename the Lean library), ask for their desired UpperCamelCase library name `<ProjectName>`, then:
  1. Update `name`, `defaultTargets`, and `[[lean_lib]] name` in `lakefile.toml` (or `lakefile.lean`).
  2. Rename `ExampleLibrary.lean` to `<ProjectName>.lean` and `ExampleLibrary/` to `<ProjectName>/`, updating all `import` paths (e.g., `public import <ProjectName>.Test`).
  3. Run `lake build` to confirm the renamed library compiles cleanly.
- **Configure `.tinytau/config.yml`**: Help set `human-repo`, `human-branch`, `human-directory`, `sync-min-interval`, and `bump` (`true`/`false`), and confirm whether the sample `roadmap/` files should be kept or replaced by an initial `Sync`.
- **Install or Fix Missing Tools**: For any missing required tool—or any optional tool the user chooses to enable locally (such as Quarto for local roadmap preview, `rg`, or `lean-lsp-mcp`)—give concise OS-specific setup instructions and offer to re-run the affected check.
