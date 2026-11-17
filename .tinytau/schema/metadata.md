---
name: Metadata Schemas
description: Defines the schemas for *-ai.yml sidecar files, roadmap frontmatter (.qmd/.md/<stem>.yml), and .tauwanted files.
---

## Metadata File (`*-ai.yml`)

Tracks **planning dependencies** (guiding formalization order, not required to mirror every low-level logical dependency in Lean) and **formalization progress** linked to [`doc-gen4`](https://github.com/leanprover/doc-gen4) declarations.

```yaml
- id: thm-main
  ok: true
  depends:
    - /roadmap/area/topic.qmd#def-basic
    - /roadmap/area/topic-ai.qmd#lem-helper
    - /roadmap/area/foundations/extra-ai.qmd
  docs:
    - /docs/ProjectName/Area/Topic.html#ProjectName.Area.thm_main
    - /docs/ProjectName/Area/Defs.html
  comment: Requires def-basic and lem-helper; formalized as ProjectName.Area.thm_main assuming [FiniteDimensional K V].
```

| Field | Required | Type | Description |
| :--- | :--- | :--- | :--- |
| `id` | Yes | `string` | Fenced div ID (without leading `#`) in the paired `.qmd` or `-ai.qmd` file. |
| `ok` | Yes | `true` \| `false` \| `refactor` | Formalization state (see below). |
| `depends` | Yes | `list[string]` | Root-relative `/roadmap/...` planning dependencies (`.../file.qmd#target-id` or `.../file.qmd`); `[]` if none. |
| `docs` | Yes | `list[string]` | Root-relative `doc-gen4` paths (`/docs/<ModulePath>.html#<DeclarationName>` or `/docs/<ModulePath>.html`). Must be `[]` when `ok: false`; may keep existing `/docs/...` paths when `ok: refactor`. |
| `comment` | Yes | `string` | Summary of planning dependencies, key typeclass/representation choices, or remaining/refactoring work when `ok` is `false` or `refactor`. |

### Values of `ok`

- **`true`**: Completely formalized, compiles without `sorry` or custom `axiom`s, and faithfully matches the mathematical target.
- **`refactor`**: An existing formalization needs repair or cleanup (for example, after an upstream roadmap edit, a doc–code mismatch, duplication, or a documented follow-up).
- **`false`**: Not yet formalized or still in progress.

## Roadmap Frontmatter (`.qmd`, `.md`, `<stem>.yml`)

Embedded YAML frontmatter in `<stem>.qmd` / `<stem>.md` and a companion `<stem>.yml` in the same directory are merged for `<stem>`.

```yaml
title: Spectral Theory
description: Compact self-adjoint operators and the spectral theorem.
tinytau: true
```

| Field | Required | Type | Description |
| :--- | :--- | :--- | :--- |
| `title` | Recommended (human); Yes (`*-ai.qmd`) | `string` | Document title used for progressive disclosure. |
| `description` | Recommended (human); Yes (`*-ai.qmd`) | `string` | Concise summary of contents (`abstract` is accepted as an alias) for progressive disclosure. |
| `tinytau` | No | `boolean` | `true` opts `<stem>` (and all sibling extensions) into formalization; `false` explicitly opts out, overriding `.tauwanted`. |

## Scope Control File (`.tauwanted`)

Human-authored, read-only control file placed at any directory level under `roadmap/` to set default formalization opt-ins.

```gitignore
# Formalize all Quarto documents in this subtree by default
*.qmd
# Exclude a specific file
!scratch.qmd
```

- **Syntax**: `.gitignore`-style line-based patterns (blank lines ignored, `#` comments, globs relative to the `.tauwanted` file's directory, `!pattern` negations).
- **Inheritance**: Deeper `.tauwanted` files inherit parent rules and can extend or negate them.
- **Exclusions**: Dotfiles (`.*`, such as `.tauwanted`) and `.yml` files (such as `_quarto.yml` and `<stem>.yml`) are configuration/metadata only and are never treated as standalone formalization targets, even if matched by a broad pattern like `*`.
- **Recommended Configuration**: Root `.tauwanted` with `*.qmd` to mark all Quarto documents as `tinytau: true` by default, and explicit `tinytau: false` in any `<stem>.qmd` or `<stem>.yml` to opt out. For other file types (e.g. `tex`, `.pdf`), explicitly write `tinytau: true` in `<stem>.yml` to opt in.
