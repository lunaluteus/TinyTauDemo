---
name: TinyTau Roadmap Navigation
description: Read roadmap/ and linked Lean modules using progressive disclosure so you only load what your task needs.
---

1. **Map `roadmap/`**: List files under `roadmap/` to separate human-authored files (no `-ai` stem suffix) from AI-maintained files (`*-ai.qmd`, `*-ai.yml`).
2. **Scan Frontmatter & Scope**: Read `.tauwanted` defaults and YAML frontmatter (`title`, `description`/`abstract`, `tinytau`) across `.qmd`, `.md`, and companion `<stem>.yml` files per [`schema/metadata.md`](/.tinytau/schema/metadata.md) and [`schema/roadmap.md`](/.tinytau/schema/roadmap.md) to locate formalizable areas.
3. **Inspect Metadata**: Read `*-ai.yml` (per [`schema/metadata.md`](/.tinytau/schema/metadata.md)) in that area to find `ok: false` or `ok: refactor` targets, check `depends` readiness, and find `/docs/...` links in `docs` to already formalized dependencies.
4. **Read Target Exposition**: Open only the relevant `::: {#id}` fenced divs and surrounding context for your target and its direct dependencies.
5. **Inspect Lean Sources**: Open only the Lean files referenced by those dependencies.
