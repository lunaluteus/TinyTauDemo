---
name: Lean Build and Verification Standard
description: Defines the Lean verification requirements enforced by GitHub Actions.
---

Lean verification satisfies the requirements enforced by [`.github/workflows/lean-action.yml`](/.github/workflows/lean-action.yml) when both checks pass.

1. **Warning-Free Build**: `lake build --wfail` succeeds with zero errors and zero warnings (`build-args: "--wfail"`).
2. **Standard Axioms Only**: All declarations depend only on `propext`, `Classical.choice`, and `Quot.sound` (`axiom-audit-allow: "propext,Classical.choice,Quot.sound"`). Do not leave `sorry` / `admit` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`), or custom `axiom`s; CI verifies this via `axiom-audit`.
