/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Integer.PrimitiveFermatSolution
import Mathlib.NumberTheory.FLT.Four

/-!
# Fermat's theorem at exponent four

Mathlib's `not_fermat_42` rules out integer solutions with nonzero first and second
coordinates to `x ^ 4 + y ^ 4 = z ^ 2`. This module applies it to primitive solutions.
See `/roadmap/index.qmd#thm-fermat-n4 @ 604313ad294d7bf5ccda3184dcdbecd4af677af2`.
-/

namespace TinyTauDemo

/-- The exponent-four Fermat equation has no primitive integer solutions. -/
public theorem not_primitiveFermatSolution_four_int (x y z : ℤ) :
    ¬ PrimitiveFermatSolution 4 x y z := by
  intro h
  exact not_fermat_42 (c := z ^ 2) h.x_ne_zero h.y_ne_zero (by
    simpa only [← pow_mul] using h.eq)

end TinyTauDemo
