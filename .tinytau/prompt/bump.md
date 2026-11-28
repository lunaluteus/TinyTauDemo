---
name: Bump
description: Upgrade the upstream TauCeti dependency when a new stable Lean release tag is available, get the build green quickly, and record any newly redundant or unsuitable code for follow-up refactoring.
---

## Goal

Adopt the new stable `TauCeti` release (`<latest-upstream-tag>`) rapidly and cleanly. Prioritize passing [`guide/check.md`](/.tinytau/guide/check.md) first; defer larger cleanups or deduplications of newly redundant local code to follow-up `Refactor` commits by recording `ok: refactor` in `*-ai.yml`.

## Procedure

1. **Inspect Upstream Release Pin**: Using `<latest-upstream-tag>` discovered during mode selection in [`worker.md`](./worker.md), inspect `TauCeti`'s `lean-toolchain` at `<latest-upstream-tag>`:

   ```sh
   git fetch --depth 1 https://github.com/TauCetiProject/TauCeti.git tag <latest-upstream-tag>
   git show <latest-upstream-tag>:lean-toolchain
   ```

2. **Update Pins & Manifest**:

   - Update `TauCeti`'s `rev` in `lakefile.toml` (or `lakefile.lean`) to `"<latest-upstream-tag>"`.
   - Update `lean-toolchain` to match `TauCeti`'s `lean-toolchain` at `<latest-upstream-tag>`.
   - Refresh dependencies (and fetch cached artifacts if available):

     ```sh
     lake update TauCeti
     ```

3. **Adapt & Verify Build First**:

   - Run `lake build --wfail` and fix any breaking changes introduced by the upgraded `TauCeti` / `Mathlib` / Lean toolchain (e.g., renamed/moved upstream declarations, changed signatures or typeclass instances, or new linter errors).
   - Keep changes minimal and focused on getting the build green. Do **not** block the bump on large-scale local deduplication or rewrites.

4. **Record Newly Redundant or Unsuitable Code as `ok: refactor`**:

   - Review local Lean declarations and proofs that interact with updated `TauCeti` / `Mathlib` APIs (or compare against newly added upstream declarations).
   - If existing formalized code has become duplicated by `TauCeti` / `Mathlib`, superseded by cleaner upstream abstractions, or burdened by temporary compatibility workarounds from the bump:
     - Leave working code in place unless replacing/removing it is trivial and self-contained.
     - Mark the corresponding target(s) in `roadmap/**/*-ai.yml` as `ok: refactor` (preserving existing `docs` paths per [`schema/metadata.md`](/.tinytau/schema/metadata.md)), and note in `comment` what became redundant/unsuitable and which upstream declarations supersede it.

5. **Self-Check & Commit**:

   - Verify that no human-authored `roadmap/` files or `.tinytau/sync.yml` were modified, and verification passes cleanly.
   - Review your changes against [`guide/rubrics.md`](/.tinytau/guide/rubrics.md) and commit per [`worker.md`](./worker.md#committing-work).
