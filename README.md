# TinyTau

TinyTau is a lightweight, out-of-the-box continuous Lean 4 formalization workflow for individual researchers to **progressively** formalize their mathematical research with minimal human intervention.

See the Demo repository at [sun123zxy/TinyTauDemo](https://github.com/sun123zxy/TinyTauDemo).

## Philosophy

Inspired by the [Tau Ceti](https://github.com/TauCetiProject/TauCeti) project, TinyTau also takes a roadmap-driven approach. The difference is:

- **We allow you to write your roadmap progressively.** Write your papers, lecture notes, and roadmaps at your own pace using the TinyTau roadmap schema. Let your AI agent maintain a **superset** of your work, progressively formalizing your mathematics in Lean 4. Human attention is not a bottleneck of the process.

- **We choose to be "tiny".** Instead of building heavy orchestration and multi-agent PR review pipelines, we trust your coding agent's ability to autonomously formalize your roadmap. A Sol-level AI agent should be able to handle this task.

## What we provide

In a nutshell, TinyTau provides:

- **A flexible, human-first roadmap schema** to bridge the gap between informal human mathematical writings to relatively formal formalization blueprints.

  We do not require you to write your roadmap in a specific style or format (though we recommend Pandoc's or Quarto's Markdown). AI maintains a **superset** of their work, addressing ambiguities, skipped prerequisites, and the proof DAG (Directed Acyclic Graph). The TinyTau schema links your writings to their formalization, allowing you to track the progress easily.

- **Basic prompt engineering** for a single powerful AI coding agent to autonomously formalize the blueprints progressively with minimal human intervention.

  Including syncing with human-authored roadmap files, writing Lean 4 code, self-checking against quality rubrics, and bumping upstreams like Mathlib and Tau Ceti. Our prompts are minimal, so you can easily customize them to your own needs.

## A Glimpse of the File Structure

The following shows a typical TinyTau repository structure. Indeed, this repository is itself a TinyTau template for your own project.

```sh
.tinytau/                      # TinyTau schema, config, agent prompts, and quality guides
.github/workflows/             # GitHub Actions CI workflow files
roadmap/                       # Superset of human-authored roadmap files (TinyTau schema)
  .tauwanted                   # Human-authored, read-only control file for formalization scope.
                               # Similar to .gitignore, e.g. set `*.qmd` to include all `.qmd` files by default
  area1/
    topic.qmd                  # Human-authored
    figure.png                 # Human-authored
    topic-ai.qmd               # AI-maintained, refinement / formalization notes for `topic.qmd`
    topic-ai.yml               # AI-maintained, planning dependencies and formalization status for `topic.qmd` & `topic-ai.qmd`
    paper.pdf                  # Human-authored, a roadmap need not be a `qmd`
    paper.yml                  # Human-authored, write `tinytau: true` to opt-in for formalization
    paper-ai.qmd               # AI-maintained, possibly OCRed and parsed version of `paper.pdf` for formalization
    paper-ai.yml               # AI-maintained, planning dependencies and formalization status for `paper-ai.qmd`
    foundations/               # AI may freely create new directories
      extra-ai.qmd             # AI-maintained supplementary theory for formalization
      extra-ai.yml             # Planning dependencies and formalization status for extra-ai.qmd
    _quarto.yml                # Quarto project config, for rendering and website generation
  area2/                       # AI may freely create new directories
    topic2-ai.qmd
    topic2-ai.yml
AGENTS.md                      # Entry point for your AI agent
YourLibrary/                   # AI-maintained Lean 4 library for your formalization project
YourLibrary.lean               # Lean 4 entrypoint for your library
lakefile.toml                  # Lean 4 config file (dependency versions, build targets, etc.)
lake-manifest.json             # Lean 4 dependency lockfile
lean-toolchain                 # Lean 4 version pinning
```

## Install

Create your own repository from this template, then clone it locally. Start your agent at the root directory, and ask it to guide you through the installation. You may also start manually from `AGENTS.md`.

To let your agent work autonomously, you can use a `/goal` like "Autonomously formalize the entire roadmap until no actionable tasks are available".

## Update

To update your repository with the latest TinyTau template, the following is recommended:

```sh
git remote add tinytau git@github.com:sun123zxy/TinyTau.git # add the TinyTau template repo as a remote
git pull tinytau master --allow-unrelated-histories --no-commit # pull updates from the TinyTau template repo without committing automatically
# ASK your agent to resolve merge conflicts and commit the changes
```
