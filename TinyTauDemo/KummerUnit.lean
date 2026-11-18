/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TinyTauDemo.RegularPrime
import FltRegular.NumberTheory.Cyclotomic.Rat
import FltRegular.NumberTheory.KummersLemma.KummersLemma

/-!
# Kummer's unit lemma

`flt-regular` proves Kummer's unit lemma by constructing a cyclic extension and using
Hilbert's Theorem 94 to detect prime torsion in the class group. The statement below
uses the roadmap's regularity predicate.
See `/roadmap/index.qmd#lem-kummer-unit @ 1f04718453914632da5207485b2cde31899e3438`.
-/

namespace TinyTauDemo

open scoped NumberField

/-- A cyclotomic unit congruent to an integer modulo a regular prime is a power of a unit. -/
public theorem kummer_unit {p : ℕ} (hr : RegularPrime p) (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hcong : ∃ c : ℤ, (p : 𝓞 (CyclotomicField p ℚ)) ∣ (u - c : 𝓞 (CyclotomicField p ℚ))) :
    ∃ v : (𝓞 (CyclotomicField p ℚ))ˣ, u = v ^ p := by
  have : Fact p.Prime := ⟨hr.prime⟩
  exact eq_pow_prime_of_unit_of_congruent (K := CyclotomicField p ℚ)
    hr.ne_two hr.coprime_classNumber u hcong

end TinyTauDemo
