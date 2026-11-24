---
name: GitHub Actions and Documentation Guide
description: Explains the GitHub Actions workflows for Lean verification, roadmap integrity, and Pages deployment.
---

## GitHub Actions Workflows

- **Lean Verification** ([`lean-action.yml`](/.github/workflows/lean-action.yml)) builds the library and checks that every declaration depends only on the standard axioms, as specified in [`guide/build.md`](/.tinytau/guide/build.md).

- **Roadmap Integrity** ([`compare-human.yml`](/.github/workflows/compare-human.yml)) compares human-authored files in `roadmap/` byte-for-byte with the configured upstream tree at `human-sha` in [`.tinytau/sync.yml`](/.tinytau/sync.yml). It excludes AI-maintained files as defined in [`schema/roadmap.md`](/.tinytau/schema/roadmap.md).

- **Documentation** ([`pages.yml`](/.github/workflows/pages.yml)) builds and deploys the site on pushes to `main` or `master`. Quarto renders the roadmap into `_site/roadmap/`, using the `quarto-profile` setting when specified. The `tinytau.lua` filter adds status, links, dependencies, and notes from the `*-ai.yml` sidecars. [`docgen-action`](https://github.com/leanprover-community/docgen-action) builds and caches the Lean API reference in `_site/docs/`. The workflow also rewrites legacy root-relative roadmap links before publishing `_site/` to GitHub Pages.
