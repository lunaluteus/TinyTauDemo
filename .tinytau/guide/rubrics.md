---
name: Formalization Quality Rubrics
description: Reference quality standards for self-checking Lean 4 formalizations and roadmap updates before committing.
---

Use these rubrics as a self-check reference before committing `Feat`, `Refactor`, `Bump`, or `Sync` work.

## Correctness and Faithfulness (`correctness`)

Every new definition and theorem must faithfully capture the intended mathematics. Passing local verification ([`guide/build.md`](/.tinytau/guide/build.md)) guarantees valid, warning-free proofs using only standard axioms, not that a statement says what it should. Inspect every definition and statement adversarially: try to find a counterexample, vacuous case, or hidden narrowing.

- **No Mis-formalization**: Verify that the Lean statement matches `roadmap/`. Check quantifiers, implication directions, edge cases (empty, zero, degenerate, characteristic `p`), and underlying objects.
- **No Weakened Claims / Content in Hypotheses**: Do not make hypotheses too strong or smuggle real mathematical content into assumptions (e.g., a structure turning downstream theorems into fields rather than consequences).
- **No Vacuity or Tautology**: Avoid statements that hold trivially, definitions defeq to `True` or to their own restatement, or definitions that shift difficulty elsewhere instead of discharging it.
- **No Placeholders**: Never use `True` or any trivial stand-in in a signature or structure field.
- **No Unexercised Predicates**: Every new `Prop`-valued definition, class, or hypothesis structure should have a consuming theorem or a nontrivial witness.
- **No Over-Strong Assumptions**: Do not add typeclass or structural assumptions that narrow the claim beyond the roadmap target—unless explicitly documented as a stepping-stone lemma in `*-ai.qmd` while keeping the main target `ok: false`.
- **No Faked Prerequisites**: If a target needs a missing prerequisite, formalize the real prerequisite first rather than assuming it, bundling it as a hypothesis, or substituting a weaker stand-in.

## Reuse and Duplication (`reuse`)

Reuse existing declarations from Mathlib, Tau Ceti, and the local project instead of reinventing or wrapping them unnecessarily.

- **Direct Replacements**: Search Mathlib, Tau Ceti, and local modules before introducing a new declaration that duplicates existing mathematical content (up to renaming, definitional unfolding, symmetry/duality, or trivial bridging).
- **Proof Plumbing**: In multi-line proofs, check whether standard steps (image/preimage, `Finsupp`, `Fin` case splits, etc.) already have named lemmas.
- **Library Combinators**: Prefer existing library combinators over manually assembled definitions.
- **No In-Repo Duplication**: Avoid `private` lemmas restating public ones up to defeq, composite lemmas already closed by `@[simp]`, and `∧`-bundles of existing lemmas. (Per-type restatements or specializations of generic lemmas are acceptable when they have genuine consumers.)
- **No Compatibility Shims**: Do not keep compatibility-only aliases, wrapper declarations, forwarding modules, or deprecated shims.

## Scope: Roadmap Fit and Single Topic (`scope`)

Keep each commit focused on a single coherent topic that belongs in the repository.

- **Existing Code (`Refactor` mode)**: Refactoring, relocating, renaming, simplifying, re-proving, modestly generalizing, or fixing doc–code drift for existing material is in scope.
- **Dependency Upgrades (`Bump` mode)**: Updating `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, minimal compatibility fixes in `.lean` files, and marking newly redundant or unsuitable targets as `ok: refactor` in `*-ai.yml` is one coherent unit.
- **New Mathematical Material (`Feat` mode)**: New definitions, theorems, instances, or files must advance a specific `roadmap/` target or provide a concrete, proximate prerequisite for one. Avoid speculative theory ("might be useful later") detached from the roadmap.
- **Single Topic**: Do not bundle unrelated roadmap targets or mix opportunistic refactoring of unrelated areas with new feature work. Updating `*-ai.qmd` and `*-ai.yml` alongside the Lean code for the same target counts as one coherent unit.

## Roadmap Integrity and Soundness (`roadmap`)

Keep edits under `roadmap/` (and `.tinytau/sync.yml`) mathematically sound, properly attributed, and consistent with the Lean codebase.

- **Human File Protection**:
  - Human-authored files under `roadmap/` (files without an `-ai` stem suffix per [`schema/roadmap.md`](/.tinytau/schema/roadmap.md)) are strictly read-only except during `Sync`. `compare-human.yml` verifies byte-for-byte equality against `human-repo` at `.tinytau/sync.yml`'s `human-sha`.
  - Never modify `.tinytau/sync.yml` or human-authored files outside `Sync`.
  - Never edit `.lean` files in a `Sync` commit.
- **AI Roadmap Exposition (`*-ai.qmd`)**:
  - **No Unanchored Theory**: Every new `*-ai.qmd` file and AI-added `::: {#id}` target must name the human target(s) or concrete formalization gap it serves.
  - **Soundness & Clarity**: Definitions, assumptions, and intermediate lemmas in `*-ai.qmd` must be mathematically sound, unambiguous, and consistent with both human prose and Lean code.
- **Metadata Consistency (`*-ai.yml`)**:
  - Every `id` must match an existing `::: {#id}` fenced div in the paired roadmap file.
  - `ok` (`true` | `false` | `refactor`) must reflect reality (`ok: true` only when completely formalized; `ok: refactor` when invalidated, mismatched, or flagged for cleanup).
  - Every `/docs/...` path in `docs` must point to an actual module and declaration in the repo, and `comment`s must accurately note representation/typeclass choices or remaining work.
  - Links in `depends` must point to valid `/roadmap/...` files/targets and form an acyclic planning graph.

## Attribution (`attribution`)

Credit external formal and informal sources relied upon.

- **Formal Sources**: Credit vendored Mathlib or Tau Ceti material, copied or closely adapted formalizations, and central declarations a construction follows (routine Mathlib imports do not need special attribution).
- **Informal Sources**: Credit papers, textbooks, blueprints, lecture notes, or Zulip discussions followed.
- **No Source Laundering**: If the theorem order, notation, or proof structure closely mirrors an identifiable source, credit it even if no text was copied verbatim. Do not add artificial citations for routine, self-contained work.

## Public API (`api-design`)

Keep the public interface clean, extensional, and practical for downstream use within this repository.

- **Appropriate Visibility**: General, standalone infrastructure should be public in its canonical module rather than hidden as `private`; genuine proof-internal helpers should stay `private`. Avoid `@[expose]` unless consumers need to unfold or compute with the definition.
- **Usable Characteristic API**: Provide enough basic lemmas (introduction/elimination, `@[simp]`/`@[grind]` where helpful) so downstream code does not have to unfold definitions. Do not over-engineer exhaustive Mathlib-style API coverage if project consumers do not need it.
- **Extensionality**: Bundled definitions must not carry unconstrained free data that breaks `@[ext]` or equality reasoning.

## Generality (`generality`)

Write statements at a practical level of generality for reuse within this repository.

- **No Unused Hypotheses**: Remove assumptions that are unused or contradicted by a more general nearby theorem.
- **General-First Factoring**: Prove the general statement first and derive special cases from it, rather than duplicating proofs across special cases.
- **Balanced Abstraction**: Avoid both speculative over-abstraction (parameters with no consumer or roadmap need) and premature Mathlib-level over-generalization that stalls research progress.

## Placement and Imports (`placement`)

Place declarations in canonical modules and keep imports clean.

- **Canonical Module Home**: Place each declaration in the Lean file whose topic, abstraction level, and dependencies match it. Do not put roadmap-specific declarations in generic files, and do not hide misplaced declarations with `private`.
- **Clean Relocations**: Moving a declaration or module must update all in-repo imports in the same commit (no forwarding modules or `deprecated_module` shims).
- **Minimal Imports**: Remove unused imports and avoid broad `import Mathlib` where specific module imports suffice.

## Naming and Notation (`naming`)

Keep names and notation clear, accurate, and consistent with Lean/Mathlib conventions.

- **Clarity & Consistency**: Names should match adjacent project declarations and describe the **conclusion**, not the proof method.
- **No Overclaiming**: A name must not promise more than the statement proves (e.g., `…_iff` for a one-way implication, or `…_eq` for `≤`).
- **Dot Notation**: Declarations whose first explicit argument is an existing Lean or Mathlib type should live in that type's namespace so `x.foo` resolves cleanly.
- **Notation**: Introduce notation sparingly, make it `scoped`, and follow Mathlib precedent and precedence.

## Documentation (`documentation`)

Write accurate, concise docstrings and comments in Lean files.

- **Copyright Header**: New `.lean` files should begin with the standard copyright/author header referencing `copyright-name` from [`.tinytau/config.yml`](/.tinytau/config.yml).
- **Module Docstrings**: Substantive new Lean files should begin with a module docstring explaining what mathematical content lives there and why.
- **Public Declarations**: Document public definitions, main theorems, non-obvious abbreviations, and exported instances whose purpose is not self-evident. Describe the mathematical object or statement, not proof mechanics.
- **Commit-Pinned Roadmap References**: Lean docstrings or comments may reference `roadmap/` paths or target IDs **only** when pinned to an exact commit SHA (e.g., `/roadmap/area/topic.qmd#thm-main @ <commit-sha>`), so stale references remain detectable.
- **No Overclaiming**: Keep docstrings accurate and up to date.

## Proof Quality (`proof-quality`)

Keep proofs maintainable and readable.

- **Automation First**: Prefer robust automation (`grind`, `simp`, `omega`) over brittle chains of named-lemma rewrites.
- **Explicit Defeq Manipulation**: Avoid `change` or `show` without a comment explaining why the goal cannot be closed directly; prefer explicit lemmas over accidental definitional equality across wrappers or coercions.
- **Avoid Fragile `simpa`**: Watch for `simpa` calls that close non-obvious goals via heavy unfolding.
- **Structure & Factoring**: Extract substantial or repeated reasoning into reusable helper lemmas while keeping genuine one-offs inline. Split long proofs (> ~50 lines) into preliminary lemmas or include brief structural comments.
